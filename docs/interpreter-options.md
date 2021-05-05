# Hash language Interpretor command-line arguments

The `Hash` interpreter has a number of options that you can enable when running an instance of
a VM. This page documents options and configurations that you can change when running a `Hash`
interpreter. 

# General overview

| Argument&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;             	| Operands   	| Description                                                                                                                                                                                      	|
|-----------------------	|------------	|--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------	|
| `-e`&nbsp;`--execute` 	| `filename` 	| Set the mode of the interpreter to 'execute' mode implying to immediately run the provided script rather than launching as an interactive mode.                                               	|
| `-h`&nbsp;`--help`    	| n/a        	| Displays a help dialogue on how to use the command line arguments with the<br>hash interpreter.                                                                                                    	|
| `-i`&nbsp;`--include` 	| `dir`      	| Includes the specified directory into the module scope of the interpreter. This allows for the program to reference source files that can be many parent directories away with relative ease. 	|
| `-v`&nbsp;`--version` 	| n/a        	| Displays the current interpreter version with some additional debug information about the installed interpreter.                                                                              	|
<br/>

# Modes

## Interactive mode
To run the intrepreter, you can simply launch it within a terminal by doing so..

```
$ hash
> print("Привет κόσμος")
Привет κόσμος
```

The default arguments for the interpreter is to start within interactive mode which can be verbosely set by `-i` flag.

## Execute mode

Alterantively, you can run a hash module by specifying the `-e` and then specifying the file name. For example:

```
$ hash -e examples/compute_pi.hash
3.1415926535897
```

So essentially, this conviniently executes a given file without having to include it within the interactive mode and run functions from it.