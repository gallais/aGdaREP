# aGdaREP - Implementing grep in Agda

    Usage: aGdaREP [OPTIONS] regexp [filename]

The matching algorithm is more or less the one described in Alexandre Agular
and Bassel Mannaa's 2009 technical report ([pdf](http://www.cse.chalmers.se/~bassel/regex_agda/report.pdf)).
The major difference is probably the fact that I opted for smart constructors
rather than having a later pass simplifying the regular expression computed
by the derivative function `_⟪_`.

The development relies on the standard library ([github](https://github.com/agda/agda-stdlib))
and its ffi bindings which need to be installed separately using `cabal install` in [this
directory](https://github.com/agda/agda-stdlib/tree/master/ffi).
