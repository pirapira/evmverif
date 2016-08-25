# Formal Verification of EVM Bytecodes

## Contents
This repository contains
* a framework for specifying an Ethereum contract
* some example specifications
* EVM bytecode programs
* formal proofs that the programs satisfy the specifications.

## (Im)maturity
Don’t take it seriously yet: I haven’t checked anything
against the real implementations.
This project is still in an elementary stage.  I'd like to
* explore strategies modelling the infinite process
  (an Ethereum contract goes through unlimited number of events),
* translate more parts of the yellow paper: more instructions,
  and the gas economics
* check the translation against real blockchain data
* verify gradually more complex contracts
* develop proof methodology
* produce geth RPC command automatically so that the verified contracts can
  easily be deployed
* try out other theorem provers (maybe with better connection with SMT solvers).

## How to compile
All development is currently in [Coq](https://coq.inria.fr/).
With Coq 8.5pl2,
```
make
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
to respond to any entrance.  The contract should be ready for infinite number
of interactions (until it executes `SUICIDE`).

This idea is coinductively captured in `response_to_world` type.

## Advantages

The framework is aware of the reentrancy situations.  Reentrancy can be nested arbitrarily deeply, but the proven invariants hold still.

## Limitations

Gas is not considered among many things.  A contract in reality dies more often than described here.  For this reason, liveness properties are better tested than proven in this framework.

## Examples

`example/AbstractExamples.v`:
* `always_fail`: a contract that always fails
* `always_return`: a contract that always returns (gas is not modelled yet)

`example/call_but_fail_on_reentrance.v`:
* `call_but_fail_on_reentrance`: a contract that calls another contract but fails when the other contract calls back

`example/managed_account_with_accumulators.v`:
* `managed_account_with_accumulators`: a wallet that keeps track of the accumulated income and spending so far.  An invariant is proven that the balance is the difference between the accumulated amounts.

## License

Currently the content of this repository is distributed under
Creative Commons Attribution-ShareAlike 4.0 International License.
