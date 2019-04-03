# TheoryFSM
A theory of finite state machines and testing theories

## Overview

This project aims at formalizing and verifying the adaptive state counting algorithm in [Isabelle/HOL](http://isabelle.in.tum.de/), which incorporates several aspects:
- formalizing finite state machines themselves
- formalizing adaptive test cases
- formalizing and verifying the adaptive state counting algorithm 

### Finite state machines 

Finite state machines are introduced in [FSM.thy](FSM.thy), which formalizes several basic properties. 
Additionally, [FSM_Product.thy](FSM_Product.thy) formalizes the concept of a product machine with an explicit FAIL state, the reachability of which forms the basis of later arguments concerning testing.

### Adaptive test cases

Adaptive test cases are tree-like structures used in the adaptive state counting algorithm to prove that certain sequences reach different states. 
They are desribed in [ATC.thy](ATC.thy).

### Adaptive state counting

The adaptive state counting algorithm can be used to generate complete test suites to test whether some FSM is a reduction of another.
It essentialy performs a depth-first search to find a sequence to a failure. In doing so, it applies state counting to decide when to stop extending some sequence.
This calculation is used as the LB function in [ASC_LB.thy](ASC_LB.thy) and test suite generated in applying this approach is described in [ASC_Suite.thy](ASC_Suite.thy).
The proof that this test suite is sufficient to prove reduction is given in [ASC_Sufficiency.thy](ASC_Sufficiency.thy).
Finally, an algorithm performing this generation is presented and verified (using Hoare-Logic) in [ASC_Hoare.thy](ASC_Hoare.thy).

## Dependencies

This project depends on the [afp](https://www.isa-afp.org/index.html) entry [Transition Systems and Automata](https://www.isa-afp.org/entries/Transition_Systems_and_Automata.html) for the formalization of FSMs.
To install this entry, please follow [these instructions](https://www.isa-afp.org/using.html).

## Background

The adaptive state counting algorithm formalized in this project is a slight modification of the algorithm developed by R. M. Hierons.
The need for this modification and the modification itself have been described in my [master's thesis](doc/Master's_thesis.pdf), which also performs "on paper" most of the proofs contained in this project. 

Any reference to some lemma by a three-digit index (e.g. lemma 5.4.7) in the comments of the theories described above is a reference to the corresponding lemma in my master's thesis.




