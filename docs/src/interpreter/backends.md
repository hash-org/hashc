# Compiler backends

## Current backend

The current backend uses a Bytecode representation of the program which will run in a Virtual
machine that implements garbage collection. This is similar to Python's approach to running
programs, but however as we all know, Python is incredibly terrible for performant code 
(unless using C bindings).

We want to move away from using a Virtual machine as the main backend and actually provide
executables that can be run on `x86_64` backend using either a native (naive) backend, and
LLVM.

However, there are advantages to having a VM implementation for the language, which are 
primarily:

- We can have an interactive mode, execute code on the fly (with a minor performance hit)
- We can run compile-time code functions that are beyound just templates and constant
folding expressions.

## Planned backends

Here are the currently planned backends, that will be worked on and stabalised some time in the future:

| Name            | Description                                                                         | Target platform | Status |
|-----------------|-------------------------------------------------------------------------------------|-----------------|--------|
| `x86_64_native` | A native backend for generating executables and performing optimisations ourselves. | `x86_64`        |  ❌    |
| `x86_64_llvm`   | An backend powered by the might of LLVM backend.                                    | `x86_64`        |  ❌    |
| `vm`            | Virtual machine backend able to run bytecode compiled programs.                     | `any`           |  ✅    |
| `elf64`         | Backend for generating standalone ELFs for un-named host operating systems.         | `i386`          |  ❌    |
| `wasm`          | WebAssembly backend, convert hash programs into WebAssembly executables             | `browser/any`   |  ❌    |
| `js`            | JS backend, generate TS/JavaScript code from the provided program.                  | `browser/any`   |  ❌    |
