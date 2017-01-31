# A MAC Formalization

This project is a full formalization in Agda of [MAC](https://hackage.haskell.org/package/mac), 
an expressive programming language embedded in Haskell, that guarantees data confidentiality
*statically*.

The formalization contains all the advanced features provided by the library, including:
* Exceptions
* Mutable References
* Concurrency

The paper [*On Formalizing Information-Flow Control Libraries*](http://www.cse.chalmers.se/~russo/publications_files/plas16.pdf)
describes the techniques used to formally prove that the library is secure.

The main result of this formalization is a scheduler-parametric, *progress-sensitive* **non-interference** theorem.
