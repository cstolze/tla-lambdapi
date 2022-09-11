# An Encoding of TLA+ Set Theory in LambdaPi

This repository contains an initial attempt at encoding the set theory
of [TLA+](http://lamport.azurewebsites.net/tla/tla.html) in the proof assistant
[LambdaPi](https://github.com/Deducteam/lambdapi).

* **predicatelogic.lp** encodes (strongly untyped) predicate logic, based on
  the primitive operators *true*, *false*, and *ite* (conditional), and the
  primitive binder *choose* (Hilbert's choice).

* **settheory.lp** formalizes TLA+'s version of Zermelo-Fraenkel set theory.

* **fixedpoints.lp** proves the Knaster-Tarski fixed-point theorems.

TLA+ functions are not yet represented in the above theories.
It would also be interested to encode boolification and make better use
of LambdaPi's rewriting mechanism.
