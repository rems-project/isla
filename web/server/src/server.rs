// BSD 2-Clause License
//
// Copyright (c) 2020 Alasdair Armstrong
//
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:
//
// 1. Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//
// 2. Redistributions in binary form must reproduce the above copyright
// notice, this list of conditions and the following disclaimer in the
// documentation and/or other materials provided with the distribution.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

use std::collections::HashMap;
use std::net::SocketAddr;
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::atomic::{AtomicUsize, Ordering};

use getopts::Options;
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::process::Command;
use tokio::sync::RwLock;
use tokio::task;
use warp::reject::Rejection;
use warp::Filter;

mod request;
use request::{Request, Response};

static WORKERS: AtomicUsize = AtomicUsize::new(0);
static MAX_WORKERS: usize = 10;

async fn spawn_worker_err(config: &Config, req: &Request) -> Option<String> {
    loop {
        let num = WORKERS.load(Ordering::SeqCst);
        if num < MAX_WORKERS && WORKERS.compare_exchange(num, num + 1, Ordering::SeqCst, Ordering::SeqCst).is_ok() {
            break;
        }
        task::yield_now().await;
    }

    let mut command = Command::new(&config.worker);
    command.arg("--resources").arg(&config.resources).arg("--cache").arg(&config.cache);

    if let Some(path) = &config.litmus_convert {
        command.arg("--litmus-convert").arg(path);
    }

    if let Some(name) = &config.toolchain {
        command.arg("--toolchain").arg(name);
    }

    if let Some(value) = &config.ld_library_path {
        command.env("LD_LIBRARY_PATH", value);
    }

    let mut child = command.stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::inherit()).spawn().ok()?;

    child.stdin.take().unwrap().write_all(&bincode::serialize(&req).ok()?).await.ok()?;

    let mut stdout = child.stdout.take().unwrap();
    //let mut stderr = child.stderr.take().unwrap();

    let status = child.await.ok()?;

    let response = if status.success() {
        let mut response = Vec::new();
        stdout.read_to_end(&mut response).await.ok()?;
        String::from_utf8(response).ok()?
    } else {
        /*
        let mut log = Vec::new();
        stderr.read_to_end(&mut log).await.ok()?;
        let filename = format!("isla-error-{}.log", Utc::now().to_rfc3339());
        fs::write(config.logs.join(&filename), log).await.ok()?;
         */
        serde_json::to_string(&Response::InternalError).ok()?
    };

    let num = WORKERS.fetch_sub(1, Ordering::SeqCst);
    assert!(num != 0);

    Some(response)
}

async fn spawn_worker((config, req_cache, req): (&Config, &ReqCache, Request)) -> Result<String, Rejection> {
    let cached = {
        let cache = req_cache.read().await;
        cache.get(&req).map(String::to_owned)
    };

    match cached {
        Some(response) => Ok(response),
        None => match spawn_worker_err(config, &req).await {
            Some(response) => {
                let mut cache = req_cache.write().await;
                cache.insert(req, response.clone());
                Ok(response)
            }
            None => Err(warp::reject::reject()),
        },
    }
}

#[derive(Clone)]
struct Config {
    worker: PathBuf,
    litmus_convert: Option<String>,
    toolchain: Option<String>,
    dist: PathBuf,
    resources: PathBuf,
    cache: PathBuf,
    logs: PathBuf,
    address: SocketAddr,
    ld_library_path: Option<String>,
    tls_cert: Option<String>,
    tls_key: Option<String>,
}

fn get_config() -> &'static Config {
    let args: Vec<String> = std::env::args().collect();
    let mut opts = Options::new();
    opts.reqopt("", "worker", "path to worker process", "<path>");
    opts.optopt("", "litmus-convert", "path of .litmus to .toml converter", "<path>");
    opts.optopt("", "toolchain", "use specified toolchain from config", "<name>");
    opts.reqopt("", "dist", "path to static files", "<path>");
    opts.reqopt("", "resources", "path to resource files", "<path>");
    opts.reqopt("", "cache", "path to a cache directory", "<path>");
    opts.reqopt("", "logs", "path to logging directory", "<path>");
    opts.reqopt("", "address", "socket address to run server on", "<address:port>");
    opts.optopt("", "ld-library-path", "LD_LIBRARY_PATH for worker", "<path>");
    opts.optopt("", "tls-cert", "TLS cert file", "<path>");
    opts.optopt("", "tls-key", "TLS key file", "<path>");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error: {}\n{}", e, opts.usage("islaweb-server <options>"));
            std::process::exit(1)
        }
    };

    Box::leak(Box::new(Config {
        worker: PathBuf::from(matches.opt_str("worker").unwrap()),
        litmus_convert: matches.opt_str("litmus-convert"),
        toolchain: matches.opt_str("toolchain"),
        dist: PathBuf::from(matches.opt_str("dist").unwrap()),
        resources: PathBuf::from(matches.opt_str("resources").unwrap()),
        cache: PathBuf::from(matches.opt_str("cache").unwrap()),
        logs: PathBuf::from(matches.opt_str("logs").unwrap()),
        address: matches.opt_str("address").unwrap().parse().unwrap(),
        ld_library_path: matches.opt_str("ld-library-path"),
        tls_cert: matches.opt_str("tls-cert"),
        tls_key: matches.opt_str("tls-key"),
    }))
}

type ReqCache = RwLock<HashMap<Request, String>>;

fn create_cache() -> &'static ReqCache {
    Box::leak(Box::new(RwLock::new(HashMap::new())))
}

#[tokio::main]
async fn main() {
    let config = get_config();
    let req_cache = create_cache();

    let dist = warp::filters::query::query::<Request>()
        .map(move |req| (config, req_cache, req))
        .and_then(spawn_worker)
        .or(warp::fs::dir(&config.dist));

    if cfg!(feature = "https") {
        warp::serve(dist)
            .tls()
            .cert_path(config.tls_cert.as_ref().unwrap())
            .key_path(config.tls_key.as_ref().unwrap())
            .run(config.address)
            .await
    } else {
        warp::serve(dist).run(config.address).await
    }
}
