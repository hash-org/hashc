# Interpretor command-line arguments

The `Hash` interpreter has a number of options that you can enable when running an instance of
a VM. This page documents options and configurations that you can change when running a `Hash`
interpreter. 

# General overview

## `-e`, `--execute`: Execute a command
Set the mode of the interpreter to 'execute' mode implying to immediately run the provided script rather than launching as an interactive mode. 

For example:

```
$ hash -e examples/compute_pi.hash
3.1415926535897
```

## `-d`, `--debug`: Run compiler in debug mode
This will enable debug mode within the compiler which will mean that the compiler will verbosely report on timings, procedures and in general
what it is doing at a given moment.

## `-h`, `--help`: Print commandline help menu
Displays a help dialogue on how to use the command line arguments with the hash interpreter. 

## `-v`, `--version`: Compiler version
Displays the current interpreter version with some additional debug information about the installed interpreter.


# VM Specific options

## `-s`, `--stack-size`: Adjust vm stack size
Adjust the stack size of the Virtual Machine. Default value is `10,0000`



# Debug Modes
## `ast-gen`: Generate AST from input file only
This mode tells the compiler to finish at the Abstract Syntax Tree stage and not produce any other kind of output.

### `-v` : Whilst generating AST, output a visual representation of the AST.

### `-d` : Run in debug mode.

## `ir-gen`: : Generate IR from input file only
This mode tells the compiler to finish at the IR stage and not produce any other kind of output.

### `-v` : Whilst generating IR, output a visual representation of the IR.

### `-d` : Run in debug mode.
