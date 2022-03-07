IntuitRIL
=========

An extension of the prover [intuitR](https://github.com/cfiorentini/intuitR) to Intermediate Propositional Logics.
The prover is written in [Haskell](https://www.haskell.org/).

The directory [examples](https://github.com/cfiorentini/intuitRIL/tree/main/examples)
contains the  files obtained by running `intuitRIL` with the following input formulas in the  G&ouml;del-Dummett Logic GL:

- &not;a &or; &not;&not;a  &nbsp; &nbsp;
(directory [examples/out-jankovAxiom-GL](https://github.com/cfiorentini/intuitRIL/tree/main/examples/out-jankovAxiom-GL), see Example 3 in the paper)
- (&not;a &rarr; b &or; c )  &rarr;  (&not;a &rarr; b) &or;    (&not;a &rarr; c )  &nbsp; &nbsp;
(directory [examples/out-kpAxiom-GL](https://github.com/cfiorentini/intuitRIL/tree/main/examples/out-kpAxiom-GL)).






Haskell installation
-------------------

You have to install the [Haskell toolchain](https://www.haskell.org/downloads)
(see  the section  [Installation instructions](https://www.haskell.org/downloads#ghcup)), 
in particular:

- [GHC](https://www.haskell.org/ghc/): the Glasgow Haskell Compiler
- [cabal-install](https://cabal.readthedocs.io/en/3.6/): the Cabal installation tool for managing Haskell software.



IntuitRIL compilation
----------------------

From the  root directory (i.e., the directory containing the file  `intuitRIL.cabal`) run the command:

```console
 cabal install
```

It should be printed a message like this:

```console
 ....
 Symlinking 'intuitRIL' to '/myHome/.cabal/bin/intuitRIL'
```

This means that `intuitRIL` is the command to launch the prover. Actually,
`intuitRIL` is a symbolic link to    `/myHome/.cabal/bin/intuitRIL`; if
the command `intuitRIL` is not found you have to add the directory `/myHome/.cabal/bin/` to
your `PATH` variable (or write the complete path of the command).


To print the usage help:


```console
intuitRIL -h
```


Running
-------

The input formula must be written in a text file. A formula `F` is specified by the following syntax:

```console
  F :=     atom          // prop. variable
        |  $false        // false
        |   ~F           // not 
        |  F & F         // and
        |  F | F         // or
        |  F => F        // implication 
        |  F <=> F       // bi-implication
```
Examples of formulas:
```console
(a => b) | ( b => a )
a | (a => b | ~b)
~ a | ~~a
( ((a1 <=> a2) =>  a1 & a2 & a3) & ((a2 <=> a3)  =>  a1 & a2 & a3)  & (( a3 <=> a1)  => a1 & a2 & a3 ) )  =>  a1 & a2 & a3  
```

You can also use the [TPTP syntax](http://tptp.cs.miami.edu/TPTP/QuickGuide/Problems.html).
Examples of formulas are available in the directory [test](https://github.com/cfiorentini/intuitRIL/tree/main/test)
(files with suffix `.p`).

To decide the validity of the formula written in the file `form.p` in the logic with name `LogName`, run the command:

```console
 intuitRIL -lLogName form.p
```
If the option `-lLogName` is omitted,  the default logic  is Intuitionistic Propositional Logic;
see below the list of the implemented logics.

To generate the output files (trace, models), use the option `-t`:

```console
 intuitRIL -lLogName  -t form.p
```

A directory out-...  will be created containing  the source files (.tex and .gv).
To compile them, move into such a directory and enter the command `make`.

Note that:

-  files .tex  are compiled using  `pdflatex`.

-  files .gv   are compiled using the command `dot` of
   [Graphviz - Graph Visualization Software](https://graphviz.org/).

Both the commands `pdflatex` and `dot` must be in your PATH variable.
If something goes wrong, try to execute the commands:

```console
pdflatex your_file.tex
dot your_file.gv -Tpng -o out.png
```

**Note**  If the  text in the pdf file exceeds  the page lenght,
open the  tex file and uncomment one of the following lines:

```console
%%\pdfpagewidth 80in  
%%\pdfpagewidth 200in %% MAX WIDTH
```

Now the text in the pdf is very tiny and must be magnified.

We have implemented other different  trace levels (options `-tk`, with k=0,1,2):

```console
 intuitRIL -l LogName -t0 form.p     // minimum trace level, no output files [DEFAULT]
 intuitRIL -l LogName -t1 form.p     // medium  trace level, no output files 
 intuitRIL -l LogName -t2 form.p     // maximum trace level, no output files 
```

If you only want to clausfy the input formula, use option `-c`:

```console
 intuitRIL -c form.p
```



The examples in the directory [examples](https://github.com/cfiorentini/intuitRIL/tree/main/examples)
have be obtained by running the following command lines 
(you have to run the prover from your local directory `test` or specify the full path of the input files `.p`):

```console
intuitRIL -lgl -t jankovAxiom.p 
intuitRIL -lgl -t kpAxiom.p
```

Implemented logics
------------------



| Logic name  | Description                |
| ----------- | ---------------------------|
| `gl`        | G&ouml;del-Dummett Logic (linear models)  |
| `glk`       | G&ouml;del-Dummett Logic of depth k (linear models with depth at most k, where k&geq; 1)  |
| `jn`        | Jankov Logic (one maximal word)   |
| `kp`        | Kreisel and Putnam Logic      (*)  |

(*) Semantic condition:


 (w0 < w1)  &and;  (w0 < w2) &Implies;
 &Exists; w s.t. (w0 &leq; w) &and;  (w &leq; w1) &and; (w &leq; w2)  &and; (maxW(w) &subseteq;  maxW(w1) &cup;  maxW(w2))


where  maxW(w') is the set of maximal worlds w'' such that w' &leq; w''. Termination is not guaranteed.


Examples:

```console
 intuitRIL -lgl  form.p
 intuitRIL -lgl2 -t0 form.p
 intuitRIL -ljn -t2  form.p
 intuitRIL -lkp -t  form.p
```