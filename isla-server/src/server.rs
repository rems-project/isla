// MIT License
//
// Copyright (c) 2019 Alasdair Armstrong
//
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

use std::error::Error;
use std::path::PathBuf;
use std::process::Stdio;
use std::sync::atomic::{AtomicUsize, Ordering};

use tokio::io::AsyncWriteExt;
use tokio::process::Command;
use tokio::task;
use warp::reject::Rejection;
use warp::Filter;

mod request;
use request::Request;

static WORKERS: AtomicUsize = AtomicUsize::new(0);
static MAX_WORKERS: usize = 10;

async fn spawn_worker_err(config: &Config, req: Request) -> Result<String, Box<dyn Error>> {
    loop {
        let num = WORKERS.load(Ordering::SeqCst);
        if num < MAX_WORKERS && WORKERS.compare_and_swap(num, num + 1, Ordering::SeqCst) == num {
            break;
        }
        task::yield_now().await;
    }

    let mut child = Command::new(&config.worker).stdin(Stdio::piped()).spawn()?;

    child.stdin.take().unwrap().write_all(&bincode::serialize(&req)?).await?;

    let status = child.await?;
    println!("the command exited with: {}", status);
    Ok("{\"data\": \"test\"}".to_string())
}

async fn spawn_worker((config, req): (&Config, Request)) -> Result<String, Rejection> {
    match spawn_worker_err(config, req).await {
        Ok(response) => Ok(response),
        Err(_) => Err(warp::reject::reject()),
    }
}

#[derive(Clone)]
struct Config {
    worker: PathBuf,
    dist: PathBuf,
}

fn get_config() -> &'static Config {
    Box::leak(Box::new(Config {
        worker: PathBuf::from("target/release/islaweb-worker"),
        dist: PathBuf::from("../isla-webui/dist/"),
    }))
}

#[tokio::main]
async fn main() {
    let config = get_config();

    let dist = warp::filters::query::query::<Request>()
        .map(move |req| (config, req))
        .and_then(spawn_worker)
        .or(warp::fs::dir(&config.dist));

    warp::serve(dist).run(([127, 0, 0, 1], 3030)).await;
}
