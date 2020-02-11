use std::env;
use std::process::Command;

fn git_commit_hash() -> Option<String> {
    let output = Command::new("git").args(&["rev-parse", "HEAD"]).output().ok()?;
    String::from_utf8(output.stdout).ok()
}

fn main() {
    // We can't rely on the system having a reasonably up-to-date z3 on all linux distros, so we can
    // add a libz3.so in the project root and link using it if needed running with LD_LIBRARY_PATH
    println!("cargo:rustc-link-search=.");

    if let Some(hash) = git_commit_hash() {
        println!("cargo:rustc-env=GIT_COMMIT={}", hash)
    } else {
        println!("cargo:rustc-env=GIT_COMMIT=UNKNOWN")
    }

    // We can alternatively just download, build, and statically link z3
    if env::var("ISLA_STATIC_Z3").is_ok() {
        Command::new("./vendor.sh").output().unwrap();
        Command::new("cp").args(&["vendor/z3/build/libz3.a", "libz3.a"]).output().unwrap();

        println!("cargo:rustc-link-lib=static=stdc++");
        println!("cargo:rustc-link-lib=static=z3");
    }
}
