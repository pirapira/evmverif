(* EVM Contract Behavior Formalization *)
(* for Coq 8.5pl2 *)

(* Yoichi Hirai i@yoichihirai.com
   Creative Commons Attribution-ShareAlike 4.0 International License *)

(* This is just a sketch of an idea put together on a weekend.
   In the interactive theorem prover Coq, I (re)started reasoning
   about a contract’s behaviour where it can be called, returned
   from a call, and of course re-entered.

   My first example is a contract that always returns, for which I
   - wrote a specification [always_return]
   - wrote some EVM code [example1_program]
   - proved that the code satisfies the specification. [example1_spec_impl_match]

   Don’t take it seriously: I haven’t checked anything against the real implementation.

   - explore other strategies modelling the infinite process
     (an Ethereum contract goes through unlimited number of events),
   - translate more parts of the yellow paper: more instructions, and the gas economics
   - check the translation against real blockchain data
   - verify gradually more complex contracts
   - develop proof methodology.
*)

(* Gas is not considered among many things.  A contract in reality dies more often than described here. *)


(***
 *** Some basic <del>definitions</del> assumptions
 ***)

(* Here I'm being lazy and assuming that these things exist.
 * I hope these don't enable us to prove 0 = 1.
 *)


(* This module can be instantiated into some concrete ways and some more abstract ways. *)
(* A word can be a tuple of 256 booleans. *)
(* Alternatively a word can be thought of as some abstract values.
 * This would be interesting in bytecode analysis tools.
 *)
(* Many aspects of the EVM semantics do not care how words are represented. *)

Require Import NArith.
Require FMapList.
Require Import OrderedType.

Require Import Word.
Require Import ContractSem.

Require Import Cyclic.Abstract.CyclicAxioms.
Require Import Coq.Lists.List.

Require Import ZArith.

Require BinNums.
Require Cyclic.ZModulo.ZModulo.

(* A useful lemma to be proven *)


Require ConcreteWord.

Module ExamplesOnConcreteWord.


End ExamplesOnConcreteWord.

(* TODO: currently,
   lack of balance is treated in the semantics, but lack of gas is not.
   This discrepancy needs to be solved.
*)
