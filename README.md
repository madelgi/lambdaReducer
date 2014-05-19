# Lambda reducer

A reduction engine for the lambda calculus. Much of the included code was provided by Jim Fix.

## About

The following code includes a parser, lexer, and reduction engine for the lambda calculus.
The grammar is as follows:

```
<trm> ::= \ <name> . <trm>
<trm> ::= <trm> <trm>
<trm> ::= <name>
<trm> ::= ( <trm > )
<name> ::= <any identifier>
```

The first three grammar productions correspond to the syntax term constructors,

```
LAM : Id * Term -> Term
APP : Term * Term -> Term
Var : Id -> Term
```

For example, the terms

```
\x.x
\f.\a.f(f(f a))
\h.(\g.h(g g))(\g.h(g g))
```

correspond to the identity element, the Church numeral 3, and the Y-combinator, respectively.
Moreover, the associated syntax terms would be

```
LAM("x",VAR("x"))
LAM("f",LAM("a",APP(VAR("f"),APP(VAR("f"),APP(VAR("f"),VAR("a"))))))
LAM("h",APP(LAM("g",APP(VAR("h"),APP(VAR("g"),VAR("g")))),
            LAM("g",APP(VAR("h"),APP(VAR("g"),VAR("g"))))))
```

### Church modules

Included is the functionality of processing 'Church modules', files containing a series of lambda
definitions. For example, a Church module example.chu may contain the definitions

```
I := \x.x;
three := \f.\a.f(f(f a));
Y := \h.(\g.h(g g))(\g.h(g g));
```

If this file is loaded into the reducer, the user will be able to use 'I', 'three', and 'Y'
as shorthand for the associated lambda terms.

## Usage
First, install sbt on your system. To run the interactive reducer, simply type 'sbt run' in the
root directory. To run the reducer with a '.chu' file, type "sbt 'run <.chu file>'".

## Errors
Sometimes when using definitions from a Church module, the reduction engine functions incorrectly.

