# Formal Verification of EVM Bytecodes

This repository contains
* a framework for specifying an Ethereum contract
* some example specifications
* EVM bytecode programs
* formal proofs that the programs satisfy the specifications.

All development is currently in [Coq](https://coq.inria.fr/).
With Coq 8.5pl1,
```
coqc sketch.v
```
should type-check the definitions and the proofs.

## Behavioural Specifications

An Ethereum contract can be entered in different ways
* being called from other accounts
    * This can be re-enterance
* being returned/failed from other calls.

The contract responds to all of these by
* returning
* failing, or
* calling other accounts.

Moreover, when the contract responds, the contract should again be ready
to respond any entrance.  The contract should be ready for infinite number
of interactions (until it executes `SUICIDE`).

This idea is coinductively captured in `responce_to_world` type.
