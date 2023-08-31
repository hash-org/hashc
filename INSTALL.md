# Installing tools and dependencies

## Rust

The Rust Programming language and `cargo` are required to build the Hash compiler. The easiest way to install Rust is using [rustup](https://rustup.rs/).

## LLVM

One of the Hash compiler code generation backends is LLVM, so you will need to install LLVM on your system.
Currently, the compiler used LLVM 15.0.x, which can be installed using the following instructions 
(specific to each OS):

### MacOS

To install on MacOS, the simplest way to install it is using [Homebrew](https://brew.sh/):

```bash
brew install llvm@15
``` 
**Note**: If you are unsure of where LLVM has been installed, you can query 
the installation path using `brew --prefix llvm@15`.


### Windows

To install on Windows, the simplest way to install it is using [Chocolatey](https://chocolatey.org/):

```pwsh
choco install llvm --version 15.0.0
```

Alternatively, you can download the pre-built binaries from the [LLVM website](https://releases.llvm.org/download.html).

### Linux

To install on Linux, the simplest way to install it is using a package manager, such as `apt`, `yum`, `dnf`, etc. 

With `apt` on Ubuntu it can be installed using the following command:
```bash
add-apt-repository -y "deb http://apt.llvm.org/focal/ llvm-toolchain-focal-15 main" # Add the LLVM repository
apt update
apt install llvm-15 llvm-15-* liblld-15* libpolly-15-dev libz-dev
```

### After installation

Once the tools are installed, the LLVM binaries need to be either added to the `PATH` environment variable, or specified to `cargo` using the `LLVM_SYS_15_PREFIX` before the `cargo` command:
```
LLVM_SYS_15_PREFIX=<path_to_llvm> cargo run
``` 

However, if LLVM is added to the path, then building and testing
can be done with a simple `cargo` invocation:
