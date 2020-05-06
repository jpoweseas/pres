# pres: A CLI for all your linear integer arithmetic needs

pres is a CLI which wraps a decision algorithm for Presburger arithmetic in an easy to use REPL.

## Build instructions

Compile:

```bash
$ ghc -o pres Main.hs
```

Run REPL:
```bash
$ ./pres
```

Run on some .pres file:
```bash
$ ./pres example.pres
```

You can find some example files (with file extension .pres) in this directory. All should output false except divtest1.pres and lttest2.pres.

## Features:

The primary feature of pres is an implementation of Cooper's procedure. Cooper's procedure itself is only a quantifier elimination algorithm, so the output is a closed, quantifier-free formula which is logically equivalent to the input. Such a formula is then very easy to check. 

Formulas are represented in a Python-like expression DSL. An example of this DSL, which demonstrates most of the language features, can be seen below:

```
pres> forall x (exists y (not 2 | x + y and y < 2))
True
```

Note that | refers to divisibility. For more examples, see the given example files. You can define named subformulas on the command line using the syntax

```
pres> X := forall x (exists y (x < y))
```

which can then be incorporated in further formulas:

```
pres> X and 2 = 2
True
```

The DSL is case-sensitive: lower case identifiers correspond to function variables, upper case identifiers correspond to named subformulas. 

You can also view a named subformula as follows:

```
pres> !X
forall x (exists y (x < y))
```

The CLI also supports reading and writing to files; for a full list of command-line features, see help.txt. This information is also printed when you type :help or :h into the command line.

## Technical Details:

The REPL is implemented in *Main.hs*, which also serves as a hub for the decision procedure. Cooper's procedure is implemented in *Normalize.hs*, and exposed with the function *qe*. Cooper's procedure is typically presented in several steps, yet the function qe performs them in a single pass. The result of *qe* should then be fed into the backend of the solver. This is exposed via the *decide* function in *Solver.hs*, which evaluates a closed, quantifier-free formula as true or false. The functions in *Simplify.hs* are used throughout the pipeline to remove unneeded terms from the formulas, which attempts to mitigate exponential blowup and improve performance. 

The languages over which these transformations are performed are defined in *Lang.hs*. In particular, the *Formula a* type represents any Presburger formula, and is used for inputs to the decision procedure. This procedure outputs a quantifier-free formula, represented by *QFFormula a*, which also includes some extra language constructs for convenience. These are both quantified over the type of their atoms, which is useful in several places in the decision procedure. In general, we used the types *Formula Atom* and *QFFormula DivAtom*; the only difference between the two being that *Atoms* allow for any comparison operators, whereas *DivAtom* defines these all in terms of *<*.

Parsing of the DSL files is done in *Parse.hs*. The parsing is done using applicative parsers defined in the *Parsec library*. Before we run the decision process on a formula, we also check to make sure that the formula does not include any free variables or shadowed variables; this takes place in *Nitpick.hs*.

## References:

- http://www2.imm.dtu.dk/courses/02917/Presburger1.pdf
- https://blogg.bekk.no/creating-a-repl-in-haskell-efcdef1deec2
- https://wiki.haskell.org/Parsing_a_simple_imperative_language#Main_parser
