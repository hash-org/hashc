# Installing tools and dependencies

## Rust

The Rust Programming language and `cargo` are required to build the Hash
compiler. The easiest way to install Rust is using [rustup](https://rustup.rs/).

## LLVM

One of the Hash compiler code generation backends is LLVM, so you will need to
install LLVM on your system. Currently, the compiler uses LLVM 15.0.6.

### Building without LLVM

We all know that LLVM is a huge and bulky dependency, which isn't always easy to install on a local machine. Therefore, this project
provides a way to build the compiler without LLVM. To do so, you can simply build the main package in the following way:

```bash
cargo build -p hashc --no-default-features
```

This will build the compiler without the `llvm` feature, and hence you won't have the LLVM backend available.

### Linux, macOS

You can download this version of LLVM from
[here](https://github.com/llvm/llvm-project/releases/tag/llvmorg-18.1.8) for
your specific OS. Additionally, you need to install `zstd`  (which can be
aquired using a package manager or from
[here](https://github.com/facebook/zstd/releases/tag/v1.5.5)).

Once LLVM 18.1.8 and `zstd` are installed, you need to set the following
environment variables, replacing `$PATH_TO_LLVM` and `$PATH_TO_ZSTD`
appropriately for your system depending on your installation:

```sh
# hashc-related
export LIBRARY_PATH="$LIBRARY_PATH:$PATH_TO_ZSTD/lib"
export DYLD_LIBRARY_PATH="$DYLD_LIBRARY_PATH:$PATH_TO_LLVM/lib"
export LDFLAGS="-L$PATH_TO_LLVM/lib"
export CPPFLAGS="-I$PATH_TO_LLVM/include"
export PATH="$PATH:$PATH_TO_LLVM/bin"
export LLVM_SYS_181_PREFIX="$PATH_TO_LLVM"
```

This can be put in your shell script startup file
(`.zprofile`/`.bash_profile`/etc), or in a shell script and you can `source` it
whenever you want to use `hashc` (the former is recommended).

Now, you should be able to run `cargo build` on `hashc` and it should work.

### Windows

To install on Windows, the simplest way to install it is using
[Chocolatey](https://chocolatey.org/):

```pwsh
choco install llvm --version 18.1.8
```

Alternatively, you can download the pre-built binaries from the [LLVM
website](https://releases.llvm.org/download.html).

