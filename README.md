# aGdaREP - Implementing grep in Agda

    Usage: aGdaREP [OPTIONS] regexp [filename]

![screenshot](screenshot.png)


Requirements
------------

This project should compile using:

* Agda version 2.6.1
* The standard library (dev version)
* [Agdarsec](https://github.com/gallais/agdarsec) (dev version)


Implementation details
----------------------

The matching algorithm is more or less the one described in Alexandre Agular
and Bassel Mannaa's 2009 technical report ([pdf](http://itu.dk/people/basm/report.pdf)).
I depart from it in two occasions: firstly, I use smart constructors rather
than having a later pass simplifying the regular expression computed by the
derivative function `_⟪_`; and secondly I replace the notions of the empty
language and the language of all one letter long words by the more general
idea of ranges ("any of" and "any but").

The development relies on the standard library ([github](https://github.com/agda/agda-stdlib))
and its ffi bindings which need to be installed separately using `cabal install` in [this
directory](https://github.com/agda/agda-stdlib/tree/master/ffi).
