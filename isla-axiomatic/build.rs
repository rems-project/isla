fn main() {
    lalrpop::process_root().unwrap();
    // We can't rely on the system having a reasonably up-to-date z3
    // on all linux distros, so we can add a libz3.so in the project
    // root and link using it if needed running with LD_LIBRARY_PATH
    println!("cargo:rustc-link-search=..")
}
