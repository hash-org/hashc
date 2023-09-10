fn main() {
    // Run the `GPERF` command to generate the hash table
    // and compile it into a static library.
    println!("cargo:rerun-if-changed=keywords/hash.gperf");

    // Execute `keywords/generate.sh`
    std::process::Command::new("keywords/generate.sh")
        .status()
        .expect("Failed to execute keywords/generate.sh");

    // Compile the hash table into a static library.
    cc::Build::new().file("keywords/hash.c").opt_level(3).compile("keywords");
}
