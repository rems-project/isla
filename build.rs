use std::process::Command;
use std::env;

fn main() {
    // We can't rely on the system having a reasonably up-to-date z3 on all linux distros, so we can
    // add a libz3.so in the project root and link using it if needed running with LD_LIBRARY_PATH
    println!("cargo:rustc-link-search=.");

    // We can alternatively just download, build, and statically link z3
    if env::var("ISLA_STATIC_Z3").is_ok() {
        Command::new("./vendor.sh").output().unwrap();
        Command::new("cp").args(&["vendor/z3/build/libz3.a", "libz3.a"]).output().unwrap();

        println!("cargo:rustc-link-lib=static=stdc++");
        println!("cargo:rustc-link-lib=static=z3");
    }
}
