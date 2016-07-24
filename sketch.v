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

Module AbstractExamples (W : Word).
  Module C := (ContractSem.Make W).
  Import C.
(**** Now we are able to specify contractsin terms of how they behave over
      many invocations, returns from calls and even re-entrance! ***)

(* Example 0: a contract that always fails *)
CoFixpoint always_fail :=
  ContractAction ContractFail
                 (Respond (fun _ => always_fail)
                          (fun _ => always_fail)
                          always_fail).

(* Example 1: a contract that always returns *)
CoFixpoint always_return x :=
  ContractAction (ContractReturn x)
         (Respond (fun (_ : call_env) => always_return x)
                  (fun (_ : return_result) => always_return x)
                  (always_return x)).

(* Example 2: a contract that calls something and then returns, but fails on re-entrance *)

Section FailOnReentrance.

Variable something_to_call : call_arguments.

CoFixpoint call_but_fail_on_reentrance (depth : nat) :=
  match depth with
  | O =>
    Respond
      (fun _ =>
         ContractAction (ContractCall something_to_call)
              (call_but_fail_on_reentrance (S O)))
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance O))
      (ContractAction ContractFail (call_but_fail_on_reentrance O))
  | S O => (* now the callee responds or reenters *)
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance (S O)))
      (fun retval => ContractAction (ContractReturn retval) (call_but_fail_on_reentrance O))
      (ContractAction ContractFail (call_but_fail_on_reentrance O))
  | S (S n) =>
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance (S (S n))))
      (fun retval => ContractAction ContractFail (call_but_fail_on_reentrance (S n)))
      (ContractAction ContractFail (call_but_fail_on_reentrance (S n)))
  end.

End FailOnReentrance.

(******* Example 3.
  When re-entrance happens to the contract at example 2. ***)

Section Example3.

  Variable e : call_env.
  Variable a : call_arguments.

  Let example3_world :=
    WorldCall e :: WorldCall e :: nil.

  Let example2_contract :=
    call_but_fail_on_reentrance a 0.

  Let example3_history := specification_run example3_world example2_contract.

  Eval compute in example3_history.
(*
     = ActionByWorld (WorldCall e)
       :: ActionByContract (ContractCall a)
          :: ActionByWorld (WorldCall e)
             :: ActionByContract ContractFail :: nil
     : history

*)

End Example3.

Section Example0Continue.

  Definition spec_example_0 : response_to_world :=
    Respond
      (fun _ => always_fail)
      (fun _ => always_fail)
      always_fail.

  Variable example0_address : address.

  Definition example0_program :=
    PUSH1 (word_of_N 0) ::
    JUMP :: nil.

  Definition example0_account_state (bal : word) :=
    {| account_address := example0_address ;
       account_storage := empty_storage ;
       account_code := example0_program ;
       account_balance := bal ;
       account_ongoing_calls := nil |}.


  Require Coq.Setoids.Setoid.

  Lemma always_fail_eq :
    forall act continuation,
      always_fail = ContractAction act continuation ->
      act = ContractFail /\
      continuation = Respond (fun _ => always_fail)
                             (fun _ => always_fail)
                             always_fail.
  Proof.
    intros ? ?.
    rewrite <- (contract_action_expander_eq always_fail) at 1.
    intro H.
    inversion H.
    auto.
  Qed.

  (** learned from https://github.com/uwplse/verdi/blob/master/PROOF_ENGINEERING.md **)
  Ltac always_fail_tac :=
    match goal with
      [ H: always_fail = ContractAction ?act ?continuation |- _ ] =>
      apply always_fail_eq in H; destruct H; subst
    end.


  Search _ (N -> N -> bool).

  (* should be moved to Word *)
  Axiom smaller_word_of_N :
    forall x y,
    x < 100000 ->
    y < 100000 ->
    word_smaller (word_of_N x) (word_of_N y) = (N.ltb x  y).

  Theorem example0_spec_impl_match :
    forall bal,
      account_state_responds_to_world
        (example0_account_state bal) spec_example_0 (fun _ _ => True).
  Proof.
    cofix.
    intro bal.
    apply AccountStep.
    {
      intros ? ? ?.
      split; [solve [auto] | ].
      intros _ ?.
      always_fail_tac.
      eexists.
      eexists.
      eexists.
      split.
      {
        intros steps.
        case steps as [ | steps]; [ try left; auto | ].
        case steps as [ | steps]; [ try left; auto | ].
        { simpl.
          rewrite smaller_word_of_N; auto; compute; auto. }
        simpl.
        rewrite smaller_word_of_N; try solve [compute; auto].
        simpl.
        rewrite N_of_word_of_N; solve [compute; auto].
      }
      {
        apply example0_spec_impl_match.
      }
    }
    {
      unfold respond_to_return_correctly.
      intros rr venv continuation act.
      unfold example0_account_state.
      unfold build_venv_returned.
      simpl.
      congruence.
    }
    {
      unfold respond_to_fail_correctly.
      intros venv continuation act.
      unfold example0_account_state.
      unfold build_venv_fail.
      simpl.
      congruence.
    }
  Qed.

End Example0Continue.


Section Example1Continue.
(*** prove that example 1 has an implementation  *)

  Definition return_result_nil : return_result := nil.
  Definition action_example_1 :=
    always_return return_result_nil.

  Definition spec_example_1 : response_to_world :=
    Respond
      (fun _ => action_example_1)
      (fun _ => action_example_1)
      action_example_1.

  Variable example1_address : address.

  Definition example1_program : list instruction :=
    PUSH1 word_zero ::
    PUSH1 word_zero ::
    RETURN ::
    nil.

  Definition example1_account_state bal :=
    {| account_address := example1_address ;
       account_storage := empty_storage ;
       account_code := example1_program ;
       account_balance := bal ;
       account_ongoing_calls := nil |}.

  Lemma always_return_def :
    forall x,
      always_return x =
      ContractAction (ContractReturn x)
                     (Respond (fun (_ : call_env) => always_return x)
                              (fun (_ : return_result) => always_return x)
                              (always_return x)).
  Proof.
    intro x.
    rewrite <- (contract_action_expander_eq (always_return x)) at 1.
    auto.
  Qed.

  Lemma always_return_eq :
    forall act continuation x,
      always_return x = ContractAction act continuation ->
      act = ContractReturn x /\
      continuation = Respond (fun _ => always_return x)
                             (fun _ => always_return x)
                             (always_return x).
  Proof.
    intros ? ? ?.
    rewrite always_return_def at 1.
    intro H.
    inversion H; subst.
    auto.
  Qed.

  (** learned from https://github.com/uwplse/verdi/blob/master/PROOF_ENGINEERING.md **)
  Ltac always_return_tac :=
    match goal with
      [ H: always_return ?x = ContractAction ?act ?continuation |- _ ] =>
      apply always_return_eq in H; destruct H; subst
    end.



  Theorem example1_spec_impl_match :
    forall bal,
    account_state_responds_to_world
      (example1_account_state bal) spec_example_1 (fun _ _ => True).
  Proof.
    cofix.
    intro bal.
    apply AccountStep.
    { (* call case *)
      unfold respond_to_call_correctly.
      intros.
      split; [solve [auto] | ].
      intros _.
      eexists.
      eexists.
      eexists.
      split.
      {
        intro.
        assert (Z : word_smaller word_zero (word_of_N 256) = true).
        {
          unfold word_zero.
          rewrite smaller_word_of_N; compute; auto.
        }
        case steps as [|steps]; [left; auto | ].
        case steps as [|steps]; [left; auto | ].
        {
          simpl.
          rewrite Z.
          auto.
        }
        case steps as [|steps]; [left; auto | ].
        { simpl.
          rewrite Z.
          simpl.
          rewrite Z.
          simpl.
          auto.
        }
        unfold action_example_1 in H.
        always_return_tac.
        right.
        simpl.
        rewrite Z.
        simpl.
        rewrite Z.
        simpl.
        f_equal.
        f_equal.
        simpl.
        rewrite cut_memory_zero_nil.
        auto.
      }
      {
        unfold action_example_1 in H.
        always_return_tac.
        apply example1_spec_impl_match.
      }
    }
    {
      intros ? ? ? ?.
      simpl.
      congruence.
    }
    {
      intros ? ? ?.
      simpl.
      congruence.
    }
  Qed.

End Example1Continue.

End AbstractExamples.


Require Import Cyclic.Abstract.CyclicAxioms.
Require Import Coq.Lists.List.

  Require Import ZArith.

  Require BinNums.
  Require Cyclic.ZModulo.ZModulo.


(* A useful lemma to be proven *)
Lemma addsub :
  forall x y z,
    ZModulo.add (ZModulo.sub x y) z =
    ZModulo.sub (ZModulo.add x z) y.
Proof.
(* TODO: prove *)
Admitted.

Lemma addK :
  forall a b, ZModulo.sub (ZModulo.add a b) b = a.
Proof.
(* TODO: prove *)
Admitted.

Lemma addC (* This lemma should not enter Word. *) :
  forall a b, ZModulo.add a b = ZModulo.add b a.
Proof.
(* TODO: prove *)
Admitted.

Module ConcreteWord <: Word.

  Module WLEN <: Cyclic.ZModulo.ZModulo.PositiveNotOne.
    Import BinNums.

    Definition p : positive := xO (xO (xO (xO (xO (xO (xO (xO xH))))))).
    Lemma not_one : p <> 1%positive.
      unfold p.
      congruence.
    Qed.
  End WLEN.

  Module BLEN <: Cyclic.ZModulo.ZModulo.PositiveNotOne.
    Import BinNums.

    Definition p : positive := xO (xO (xO xH)).
    Lemma not_one : p <> 1%positive.
      unfold p.
      congruence.
    Qed.
  End BLEN.

  Module ALEN <: Cyclic.ZModulo.ZModulo.PositiveNotOne.
    Import BinNums.

    Definition p : positive := 160.
    Lemma not_one : p <> 1%positive.
      unfold p.
      congruence.
    Qed.
  End ALEN.

  Module W := Cyclic.ZModulo.ZModulo.ZModuloCyclicType WLEN.

  Module B := Cyclic.ZModulo.ZModulo.ZModuloCyclicType BLEN.

  Module A := Cyclic.ZModulo.ZModulo.ZModuloCyclicType ALEN.

  Definition word := W.t.

  Definition word_eq (a : W.t) (b : W.t) :=
    match ZnZ.compare a b with Eq => true | _ => false end.

  Definition word_add (a b : W.t) :=
    ZnZ.add a b.

  Arguments word_add a b /.

  Definition word_mul (a b : W.t) := ZnZ.mul a b.

  Definition word_sub := ZnZ.sub.

  Definition word_one := ZnZ.one.

  Definition word_zero := ZnZ.zero.

  Definition word_iszero := ZnZ.eq0.

  Definition word_smaller a b :=
    match ZnZ.compare a b with Lt => true | _ => false end.

  Definition word_smaller_or_eq a b :=
    match ZnZ.compare a b with Lt => true | Eq => true | Gt => false end.

  Definition word_of_N := Z.of_N.

  Definition N_of_word w := Z.to_N (ZnZ.to_Z w).

  Open Scope N_scope.
  Lemma N_of_word_of_N :
    forall (n : N), n < 10000 -> N_of_word (word_of_N n) = n.
  Proof.
    intros n nsmall.
    unfold N_of_word.
    unfold word_of_N.
    unfold ZnZ.to_Z.
    simpl.
    unfold ZModulo.to_Z.
    unfold ZModulo.wB.
    unfold WLEN.p.
    unfold DoubleType.base.
    rewrite Z.mod_small.
    { rewrite N2Z.id.
      reflexivity. }
    split.
    {
      apply N2Z.is_nonneg.
    }
    {
      eapply Z.lt_trans.
      { apply N2Z.inj_lt.
        eassumption. }
      vm_compute; auto.
    }
  Qed.


  Module WordOrdered <: OrderedType.
  (* Before using FSetList as storage,
     I need word as OrderedType *)


      Definition t := W.t.
      Definition eq a b := is_true (word_eq a b).
      Arguments eq /.

      Definition lt a b := is_true (word_smaller a b).
      Arguments lt /.


      Lemma eq_refl : forall x : t, eq x x.
      Proof.
        intro.
        unfold eq.
        unfold word_eq.
        simpl.
        rewrite ZModulo.spec_compare.
        rewrite Z.compare_refl.
        auto.
      Qed.

      Lemma eq_sym : forall x y : t, eq x y -> eq y x.
      Proof.
        intros ? ?.
        simpl.
        unfold word_eq. simpl.
        rewrite !ZModulo.spec_compare.
        rewrite <-Zcompare_antisym.
        simpl.
        set (r := (ZModulo.to_Z ALEN.p y ?= ZModulo.to_Z ALEN.p x)%Z).
        case r; unfold CompOpp; auto.
      Qed.

      Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
      Proof.
        intros ? ? ?.
        unfold eq.
        unfold word_eq.
        simpl.
        rewrite !ZModulo.spec_compare.
        set (xy := (ZModulo.to_Z ALEN.p x ?= ZModulo.to_Z ALEN.p y)%Z).
        case_eq xy; auto; try congruence.
        unfold xy.
        rewrite Z.compare_eq_iff.
        intro H.
        rewrite H.
        auto.
      Qed.

      Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
      Proof.
        intros x y z.
        unfold lt.
        unfold word_smaller.
        simpl.
        rewrite !ZModulo.spec_compare.
        case_eq (ZModulo.to_Z ALEN.p x ?= ZModulo.to_Z ALEN.p y)%Z; try congruence.
        case_eq (ZModulo.to_Z ALEN.p y ?= ZModulo.to_Z ALEN.p z)%Z; try congruence.
        intros H I _ _.
        erewrite (Zcompare_Lt_trans); auto; eassumption.
      Qed.

      Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
      Proof.
        unfold t.
        intros x y.
        unfold lt; unfold eq.
        unfold word_smaller; unfold word_eq.
        simpl.
        case_eq (ZModulo.compare ALEN.p x y); congruence.
      Qed.

      Definition compare : forall x y : t, Compare lt eq x y.
      Proof.
        intros x y.
        unfold lt.
        case_eq (word_smaller x y); intro L.
        { apply LT; auto. }
        unfold eq.
        case_eq (word_eq x y); intro E.
        { apply EQ; auto. }
        apply GT.
        unfold word_smaller.
        unfold word_smaller in L.
        unfold word_eq in E.
        simpl in *.

        rewrite ZModulo.spec_compare in *.

        case_eq (ZModulo.to_Z ALEN.p y ?= ZModulo.to_Z ALEN.p x)%Z; try congruence.

        {
          rewrite Z.compare_eq_iff.
          intro H.
          rewrite H in E.
          rewrite Z.compare_refl in E.
          congruence.
        }
        {
          rewrite Zcompare_Gt_Lt_antisym.
          intro H.
          rewrite H in L.
          congruence.
        }
      Defined.

      Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y}.
      Proof.
        unfold eq.
        intros x y.
        case (word_eq x y); [left | right]; congruence.
      Defined.

  End WordOrdered.


  Definition raw_byte := B.t.
  Inductive byte' :=
  | ByteRaw : raw_byte -> byte'
  | ByteOfWord : word -> nat -> byte'
  .
  Definition byte := byte'.

  Definition address := A.t.

  Definition address_of_word (w : word) : address := w.

  Definition address_eq a b :=
    match ZnZ.compare a b with Eq => true | _ => false end.

  Lemma address_eq_refl :
    forall a, address_eq a a = true.
  Proof.
    intro a.
    unfold address_eq.
    rewrite ZnZ.spec_compare.
    rewrite Z.compare_refl.
    reflexivity.
  Qed.

  Definition word_nth_byte (w : word) (n : nat) : byte :=
    ByteOfWord w n.

  Axiom word_of_bytes : list byte -> word.

  Open Scope list_scope.

  Import ListNotations.
  Lemma words_of_nth_bytes :
    forall w b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31,
    b0 = word_nth_byte w 0 ->
    b1 = word_nth_byte w 1 ->
    b2 = word_nth_byte w 2 ->
    b3 = word_nth_byte w 3 ->
    b4 = word_nth_byte w 4 ->
    b5 = word_nth_byte w 5 ->
    b6 = word_nth_byte w 6 ->
    b7 = word_nth_byte w 7 ->
    b8 = word_nth_byte w 8 ->
    b9 = word_nth_byte w 9 ->
    b10 = word_nth_byte w 10 ->
    b11 = word_nth_byte w 11 ->
    b12 = word_nth_byte w 12 ->
    b13 = word_nth_byte w 13 ->
    b14 = word_nth_byte w 14 ->
    b15 = word_nth_byte w 15 ->
    b16 = word_nth_byte w 16 ->
    b17 = word_nth_byte w 17 ->
    b18 = word_nth_byte w 18 ->
    b19 = word_nth_byte w 19 ->
    b20 = word_nth_byte w 20 ->
    b21 = word_nth_byte w 21 ->
    b22 = word_nth_byte w 22 ->
    b23 = word_nth_byte w 23 ->
    b24 = word_nth_byte w 24 ->
    b25 = word_nth_byte w 25 ->
    b26 = word_nth_byte w 26 ->
    b27 = word_nth_byte w 27 ->
    b28 = word_nth_byte w 28 ->
    b29 = word_nth_byte w 29 ->
    b30 = word_nth_byte w 30 ->
    b31 = word_nth_byte w 31 ->
    word_of_bytes
    [b0; b1; b2; b3; b4; b5; b6; b7; b8; b9; b10; b11; b12; b13; b14; b15; b16;
     b17; b18; b19; b20; b21; b22; b23; b24; b25; b26; b27; b28; b29; b30; b31] =
    w.
  Admitted.

  Axiom event : Set.

  Axiom memory_state : Set.
  Axiom empty_memory : memory_state.
  Axiom cut_memory : word -> word -> memory_state -> list byte.
  Axiom cut_memory_zero_nil :
    forall start m, cut_memory start word_zero m = nil.

  Module ST := FMapList.Make WordOrdered.

  Definition storage := ST.t word.

  Eval compute in ST.key.

  Definition storage_load (k : word) (m : storage) : word :=
    match ST.find k m with
    | None => word_zero
    | Some x => x
    end.
  Definition storage_store (k : WordOrdered.t) (v : word) (orig : storage) : storage :=
    if word_eq word_zero v then
      ST.remove k orig
    else
      ST.add k v orig.

  Definition empty_storage : storage := ST.empty word.
  Lemma empty_storage_empty : forall idx : WordOrdered.t,
      is_true (word_iszero (storage_load idx empty_storage)).
  Proof.
    intro idx.
    compute.
    auto.
  Qed.

  Lemma word_of_zero :
    word_zero = word_of_N 0.
  Proof.
    auto.
  Qed.
  Lemma word_of_one :
    word_one = word_of_N 1.
  Proof.
    auto.
  Qed.

  Definition word_of_nat :=
    BinInt.Z_of_nat.
End ConcreteWord.


Module ExamplesOnConcreteWord.

  Module ConcreteSem := (ContractSem.Make ConcreteWord).
  Include ConcreteSem.

  Definition example2_program : program :=
    PUSH1 (word_of_N 0) ::
    SLOAD ::
    DUP1 ::
    PUSH1 (word_of_N 2) ::
    JUMPI ::
    PUSH1 (word_of_N 1) ::
    ADD ::
    PUSH1 (word_of_N 0) ::
    SSTORE ::
    PUSH1 (word_of_N 0) ::
    (* TODO: change some of these arguments to value, address *)
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    CALL ::
    ISZERO ::
    PUSH1 (word_of_N 0) ::
    JUMPI ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    SSTORE ::
    STOP ::
    nil.

  Variable example2_address : address.

  Definition example2_depth_n_state  (n : word) (st : account_state) :=
    (n = 0%Z /\
       st.(account_address) = example2_address /\
       is_true (ST.equal word_eq (st.(account_storage)) empty_storage) /\
       st.(account_code) = example2_program /\
       st.(account_ongoing_calls) = nil ) \/
     (n = 1%Z /\
      st.(account_code) = example2_program /\
      storage_load 0%Z (account_storage st) = 1%Z /\
      st.(account_address) = example2_address /\
      is_true (ST.equal word_eq (storage_store 0%Z 0%Z st.(account_storage)) empty_storage)  /\
      exists ve, (st.(account_ongoing_calls) = ve :: nil /\
             ve.(venv_prg_sfx) =
    ISZERO ::
    PUSH1 (word_of_N 0) ::
    JUMPI ::
    PUSH1 (word_of_N 0) ::
    PUSH1 (word_of_N 0) ::
    SSTORE ::
    STOP ::
    nil
                  /\
                  is_true (ST.equal word_eq (storage_store 0%Z 0%Z ve.(venv_storage)) empty_storage) /\
   is_true (ST.equal word_eq (venv_storage_at_call ve) empty_storage))
     )
  .


Definition something_to_call :=
     {|
     callarg_gaslimit := 0%Z;
     callarg_code := address_of_word 0%Z;
     callarg_recipient := address_of_word 0%Z;
     callarg_value := 0%Z;
     callarg_data := cut_memory 0%Z 0%Z empty_memory;
     callarg_output_begin := 0%Z;
     callarg_output_size := storage_load 0%Z empty_storage |}.

(* TODO: remove duplicate somehow *)
CoFixpoint call_but_fail_on_reentrance (depth : word) :=
  if word_eq word_zero depth then
    Respond
      (fun _ =>
         ContractAction (ContractCall something_to_call)
              (call_but_fail_on_reentrance word_one))
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
  else if word_eq word_one depth then
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_one))
      (fun _ => ContractAction (ContractReturn nil) (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
  else
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance depth))
      (fun retval => ContractAction ContractFail (call_but_fail_on_reentrance (word_sub depth word_one)))
      (ContractAction ContractFail (call_but_fail_on_reentrance (word_sub depth word_one))).

  Lemma call_but_fail_on_reentrace_0_eq :
    call_but_fail_on_reentrance 0%Z =
    Respond
      (fun _ =>
         ContractAction (ContractCall something_to_call)
              (call_but_fail_on_reentrance word_one))
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero)).
  Proof.
    rewrite (response_expander_eq (call_but_fail_on_reentrance 0%Z)).
    auto.
  Qed.

  Lemma call_but_fail_on_reentrace_1_eq :
    call_but_fail_on_reentrance 1%Z =
    Respond
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance word_one))
      (fun retval => ContractAction (ContractReturn nil) (call_but_fail_on_reentrance word_zero))
      (ContractAction ContractFail (call_but_fail_on_reentrance word_zero)).
  Proof.
    rewrite (response_expander_eq (call_but_fail_on_reentrance 1%Z)).
    auto.
  Qed.

  Definition example2_spec (depth: word) : response_to_world :=
    call_but_fail_on_reentrance depth.

  Lemma update_remove_eq :
    forall orig,
      is_true (ST.equal word_eq orig empty_storage) ->
      is_true
        (ST.equal word_eq
                  (storage_store 0%Z 0%Z (ST.add 0%Z 1%Z orig))
                  empty_storage).
  Proof.
    intros orig nst2.
    apply ST.equal_1.
    split.
    {
      intro k.
      unfold storage_store.
      simpl.
      split.
      { intro H.
        apply False_ind.
        case_eq (word_eq k 0%Z).
        { intro k0.
          apply ST.Raw.remove_1 in H; auto.
          { apply ST.Raw.add_sorted.
            apply ST.sorted. }
          apply ST.E.eq_sym.
          assumption.
        }
        {
          intro neq.
          unfold ST.Raw.PX.In in H.
          case H as [e H].
          apply ST.Raw.remove_3 in H.
          {
            apply ST.Raw.add_3 in H.
            {
              apply ST.equal_2 in nst2.
              case nst2 as [I _].
              generalize (I k).
              unfold ST.Raw.PX.In.
              intro I'.
              case I' as [I0 _].
              simpl in I0.
              case I0.
              {
                exists e.
                apply H.
              }
              {
                intros x J.
                eapply ST.Raw.empty_1.
                apply J.
              }
            }
            {
              intro K.
              apply ST.E.eq_sym in K.
              congruence.
            }
          }
          {
            apply ST.Raw.add_sorted.
            apply ST.sorted.
          }
        }
      }
      {
        intro H.
        apply False_ind.
        case H.
        intros x Hx.
        apply (ST.Raw.empty_1 Hx).
      }
    }
    {
      intros k e e' H I.
      apply False_ind.
      generalize I.
      unfold empty_storage.
      generalize (ST.empty_1 I).
      auto.
    }
  Qed.

  Theorem example2_spec_impl_match :
    forall st n,
          example2_depth_n_state n st ->
          account_state_responds_to_world
            st (example2_spec n%Z) (fun _ _ => True).
  Proof.
    cofix.
    intros st n n_state.
    case n_state.
    {
      intro nst.
      destruct nst as [nst0 nst1].
      case nst1 as [nst1 nst2].
      case nst2 as [nst2 nst3].
      case nst3 as [nst3 nst4].
      subst.
      clear n_state.
      subst.
      unfold example2_spec.
      rewrite call_but_fail_on_reentrace_0_eq.
      apply AccountStep.
      {
        unfold respond_to_call_correctly.
        intros ce a con.
        split; [ solve [auto] | ].
        intros _ next.
        eexists.
        eexists.
        eexists.
        split.
        {
          intro s.
          simpl.
          rewrite nst3.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          assert (stl : forall idx, storage_load idx (account_storage st) = storage_load idx empty_storage).
          {
            intro idx.
            unfold storage_load.
            apply ST.equal_2 in nst2.
            unfold ST.Equivb in nst2.
            unfold ST.Raw.Equivb in nst2.
            simpl.
            case_eq (ST.find (elt:=word) idx (account_storage st)); auto.
            intros w H.
            apply ST.find_2 in H.
            apply False_ind.
            assert (ST.Raw.PX.In idx (ST.this (account_storage st))) as K.
            {
              unfold ST.Raw.PX.In.
              exists w.
              assumption.
            }
            case nst2 as [EE _].
            rewrite EE in K.
            unfold ST.Raw.PX.In in K.
            case K.
            intros content K'.
            apply (@ST.Raw.empty_1 word idx content).
            assumption.
          }
          simpl.
          rewrite !stl.
          unfold storage_load.
          unfold empty_storage.
          simpl.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          simpl.

          set (sm0 := word_smaller _ 0%Z).

          assert (H : sm0 = false).
          {
            unfold sm0.
            unfold word_smaller.
            simpl.
            rewrite ZModulo.spec_compare.
            set (v0 := (ZModulo.to_Z _ _)%Z).
            assert (0 <= v0)%Z.
            {
              apply (ZModulo.spec_to_Z_1).
              unfold ALEN.p.
              congruence.
            }
            set (comparison := (_ ?= _)%Z).
            case_eq comparison; try congruence.
            unfold comparison.
            rewrite Z.compare_nge_iff.
            intro H'.
            apply False_ind.
            apply H'.
            apply H.
          }
          rewrite H.
          right.
          f_equal.
          rewrite <- contract_action_expander_eq in next at 1.
          inversion next; subst.
          auto.
        }
        {
          simpl.
          rewrite <- contract_action_expander_eq in next at 1.
          inversion next; subst.
          simpl.
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          right.
          split; auto.
          split; auto.
          split.
          {
            unfold storage_load.
            erewrite ST.find_1.
            { eauto. }
            apply ST.add_1.
            auto.
          }
          split; auto.
          split.
          {
            apply update_remove_eq.
            assumption.
          }
          eexists; eauto.
          split.
          {
            rewrite nst4.
            intuition.
          }
          {
            split; auto.
            split; auto.
            apply update_remove_eq.
            assumption.
          }

       (* this place should be come harder and harder as I specify the
           * state at depth 1
           *)
        }
      }
      {
        unfold respond_to_return_correctly.
        intros ? ? ? ?.
        simpl.
        rewrite nst4.
        congruence.
      }
      {
        intros ? ? ?.
        simpl.
        rewrite nst4.
        congruence.
      }
    }
    {
      intros H.
      destruct H as [n1 st_code].
      destruct st_code as [st_code st_load].
      destruct st_load as [st_load st_ongoing].
      subst.
      unfold example2_spec.
      rewrite call_but_fail_on_reentrace_1_eq.
      apply AccountStep.
      { (* call *)
        intros callenv act continuation.
        split; [solve [auto] | ].
        intros _ H.
        inversion H; subst.
        clear H.
        eexists.
        eexists.
        eexists.
        unfold build_venv_called.
        rewrite st_code.
        split.
        {
          intro s.
          repeat (case s as [| s]; [ solve [left; auto] | ]).

          simpl.
          unfold venv_first_instruction.
          rewrite st_load.
          simpl.
          rewrite st_code.
          simpl.
          right.
          eauto.
        }
        {
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          intuition.
        }
      }
      { (* return *)
        unfold respond_to_return_correctly.
        intros rr venv cont act.
        elim st_ongoing.
        intros prev prevH.
        case prevH as [st_str prevH].
        case prevH as [prevH prevH'].
        case prevH' as [prevH' prevH''].
        case prevH'' as [prevH'' prevH'''].
        simpl.
        rewrite prevH'.
        intro H.
        inversion H; subst.
        clear H.
        split; [ solve [auto] | ].
        intros _ act_cont_eq.
        eexists.
        eexists.
        eexists.
        split.
        {
          intro s.
          rewrite prevH''.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          simpl.
          right.
          f_equal.
          inversion act_cont_eq.
          auto.
        }
        {
          inversion act_cont_eq.
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          left.
          repeat (split; auto); tauto.
        }
      }
      {
        unfold respond_to_fail_correctly.
        intros venv cont act.
        case st_ongoing as [st_addr st_ongoing].
        case st_ongoing as [st_storage st_ongoing].
        case st_ongoing as [ve veH].
        case veH as [st_ongoing ve_sfx].
        case ve_sfx as [ve_sfx ve_str].
        simpl.
        rewrite st_ongoing.
        intro venvH.
        inversion venvH; subst.
        clear venvH.
        split; [ solve [auto] | ].
        intros _ act_cont_H.
        inversion act_cont_H; subst.
        clear act_cont_H.
        eexists.
        eexists.
        eexists.
        split.
        {
          intro s.
          rewrite ve_sfx.
          repeat (case s as [| s]; [ solve [left; auto] | ]).
          simpl.
          unfold compose.
          rewrite st_code.
          simpl.
          right.
          f_equal.
        }
        { (* update_account_state with contract_fail  *)
          simpl.
          apply example2_spec_impl_match.
          unfold example2_depth_n_state.
          left.
          repeat split; auto; tauto.
        }
      }
    }
  Qed.

  (** Example 4: a contract that keeps track of the accumulated income and spending.
   *
   * storage[0]: owner
   * storage[1]: income so far
   * storage[2]: spending so far
   * income so far - spending so far should coincide with the balance.
   *
   * data length 0 => receive eth; storage[1] should be incremented
   *
   * data length > 0 => not receiving eth
   * if msg.sender <> owner, abort.
   * data[0-19] is the address of recipient.
   * data[32-63] is the amount of spending.
   *
   * no particular prevention of re-entrancy.
   *)

  Definition failing_action cont : contract_behavior :=
    ContractAction ContractFail cont.

  Definition receive_eth cont : contract_behavior :=
    ContractAction (ContractReturn nil) cont.

  Definition sending_action (recipient : word) value cont : contract_behavior :=
    ContractAction (ContractCall
                      {|
                        callarg_gaslimit := 30000%Z;
                        callarg_code := address_of_word recipient;
                        callarg_recipient := address_of_word recipient;
                        callarg_value := value;
                        callarg_data := nil;
                        callarg_output_begin := 0%Z;
                        callarg_output_size := 0%Z
                      |}) cont.

  CoFixpoint counter_wallet (income_sofar : word) (spending_sofar : word)
    : response_to_world :=
    Respond
      (fun cenv =>
         match cenv.(callenv_data) with
         | nil => receive_eth (counter_wallet (word_add income_sofar cenv.(callenv_value)) spending_sofar)
         | _ =>
           if word_eq word_zero (cenv.(callenv_value)) then
             if Nat.leb 64 (List.length cenv.(callenv_data)) then
               let addr := list_slice 0 32 cenv.(callenv_data) in
               let value := list_slice 32 32 cenv.(callenv_data) in
               if word_smaller_or_eq value (word_sub (word_add income_sofar cenv.(callenv_value)) spending_sofar) then
                 sending_action addr value (counter_wallet income_sofar (word_add spending_sofar value))
               else
                 failing_action (counter_wallet income_sofar spending_sofar)
             else
               failing_action (counter_wallet income_sofar spending_sofar)
           else
             failing_action (counter_wallet income_sofar spending_sofar)
         end
      )
      (fun returned =>
         ContractAction (ContractReturn nil) (counter_wallet income_sofar spending_sofar)
      )
      (
        failing_action (counter_wallet income_sofar spending_sofar)
      ).

  Lemma counter_wallet_def :
    forall income_sofar spending_sofar,
      counter_wallet income_sofar spending_sofar =
    Respond
      (fun cenv =>
         match cenv.(callenv_data) with
         | nil => receive_eth (counter_wallet (word_add income_sofar cenv.(callenv_value)) spending_sofar)
         | _ =>
           if word_eq word_zero (cenv.(callenv_value)) then
             if Nat.leb 64 (List.length cenv.(callenv_data)) then
               let addr := list_slice 0 32 cenv.(callenv_data) in
               let value := list_slice 32 32 cenv.(callenv_data) in
               if word_smaller_or_eq value (word_sub (word_add income_sofar cenv.(callenv_value)) spending_sofar) then
                 sending_action addr value (counter_wallet income_sofar (word_add spending_sofar value))
               else
                 failing_action (counter_wallet income_sofar spending_sofar)
             else
               failing_action (counter_wallet income_sofar spending_sofar)
           else
             failing_action (counter_wallet income_sofar spending_sofar)
         end
      )
      (fun returned =>
         ContractAction (ContractReturn nil) (counter_wallet income_sofar spending_sofar)
      )
      (
        failing_action (counter_wallet income_sofar spending_sofar)
      ).
  Proof.
  Admitted.

  (* TODO: streamline this by allowing labels in JUMPDEST *)
  Definition plus_size_label : word := 13%Z.
  Arguments plus_size_label /.

  Definition counter_wallet_code : program :=
    CALLDATASIZE ::
      PUSH1 plus_size_label ::
        JUMPI ::
    (* size zero *)
    CALLVALUE ::
      PUSH1 word_zero (* storage[0] *) ::
        SLOAD ::
        ADD ::
      PUSH1 word_zero ::
        SSTORE ::
    STOP ::
    JUMPDEST (* plus_size_label *) ::
    CALLVALUE ::
      PUSH1 word_zero (* invalid destination *) ::
    (**) JUMPI ::
    (* call_value zero *)
    CALLDATASIZE ::
      PUSH1 (64%Z) ::
        instr_GT ::
      PUSH1 (0%Z) ::
        JUMPI (* data too small *) ::
    PUSH1 (0%Z) (* out size *) ::
      PUSH1 (0%Z) (* out offset *) ::
        PUSH1 (0%Z) (* out size *) ::
          PUSH1 (0%Z) (* in offset *) ::
            PUSH1 (0%Z) (* in size *) ::
              PUSH1 (32%Z) ::
                CALLDATALOAD (* value loaded *) ::
                DUP1 ::
                  PUSH1 (1%Z) ::
                    SLOAD ::
                    ADD ::
                  PUSH1 (1%Z) ::
                    SSTORE ::
                PUSH1 (0%Z) ::
                  CALLDATALOAD (* addr loaded *) ::
                  PUSH2 (30000%Z) ::
                    CALL ::
      ISZERO ::
      PUSH1 word_zero ::
        JUMPI ::
    STOP ::
    nil.


  (* TODO: I think I need to change the order of arguments of storage_load *)
  Definition counter_wallet_invariant (v : variable_env) (c : constant_env) : Prop :=
      word_add (v.(venv_balance) c.(cenv_this)) (storage_load 1%Z v.(venv_storage))
    = word_add v.(venv_value_sent) (storage_load 0%Z v.(venv_storage)).

  Axiom counter_wallet_address : address.

  Definition counter_wallet_storage (income_sofar spending_sofar : word) : storage :=
    storage_store 1%Z spending_sofar (storage_store 0%Z income_sofar (ST.empty word))
    .

  Definition counter_wallet_account_state (income_sofar spending_sofar : word) (going_calls : list variable_env) : account_state :=
    {|
      account_address := counter_wallet_address (* TODO: declare this in a section *);
      account_storage := counter_wallet_storage income_sofar spending_sofar ;
      account_code := counter_wallet_code ;
      account_balance := word_sub income_sofar spending_sofar ;
      account_ongoing_calls := going_calls
    |}
    .

  Theorem counter_wallet_correct :
    forall (income_sofar spending_sofar : word),
      account_state_responds_to_world
        (counter_wallet_account_state income_sofar spending_sofar nil)
        (counter_wallet income_sofar spending_sofar)
        counter_wallet_invariant.
    (* TODO: strengthen the statement so that coinduction goes through. *)
  Proof.
    cofix.
    intros income_sofar spending_sofar.
    rewrite counter_wallet_def.
    apply AccountStep.
    {
      unfold respond_to_call_correctly.
      intros callenv act cont.
      split.
      {
        unfold counter_wallet_invariant.
        simpl.
        unfold update_balance.
        rewrite address_eq_refl.
        unfold counter_wallet_storage.
        set (spend := storage_load 1%Z _).
        (* TODO: a geneeral lemma is needed here *)
        assert (spendH : spend = spending_sofar) by admit.
        rewrite spendH.
        set (income := storage_load 0%Z _).
        assert (incomeH : income = income_sofar) by admit.
        rewrite incomeH.
        rewrite !addsub.
        rewrite addK.
        apply addC.
      }
      {
        intro I.
        case_eq (callenv_data callenv).
        { (* input data is nil *)
          intro data_nil.
          unfold receive_eth.
          intro H.
          inversion H; subst.
          clear H.
          eexists.
          eexists.
          eexists.
          split.
          {
            intro s.
            repeat (case s as [| s]; [ solve [left; auto] | ]).
            cbn.
            assert (E : word_smaller 13%Z 256%Z = true) by (compute; auto).
            rewrite E.
            cbn.
            rewrite data_nil.
            cbn.
            repeat (case s as [| s]; [ solve [left; auto] | ]).
            cbn.
            set (smaller0 := word_smaller ZModulo.zero _).
            assert (s00 : smaller0 = true) by admit.
            rewrite s00.
            cbn.
            unfold smaller0 in s00.
            rewrite s00.
            cbn.
            right.
            reflexivity.
          }
          {
            cbn.
            unfold counter_wallet_storage.
            unfold storage_load.
            unfold ZModulo.zero.
            set (prev_income := ST.find _ _).
            assert (P : prev_income = Some income_sofar) by admit.
            rewrite P.
            set (new_income := ZModulo.add income_sofar _).
            generalize (counter_wallet_correct new_income).
            intro IH.
            unfold counter_wallet_account_state in IH.
            unfold counter_wallet_storage in IH.
            assert (II : storage_store 0%Z new_income
                         (storage_store 1%Z spending_sofar
                            (storage_store 0%Z income_sofar
                               (ST.empty word))) =
                         (storage_store 1%Z spending_sofar
                            (storage_store 0%Z new_income
                               (ST.empty word)))) by admit.
            rewrite II.
            unfold update_balance.
            set (eq_xx := address_eq _ _).
            assert (XX: eq_xx = true) by apply address_eq_refl.
            rewrite XX.
            rewrite addsub.
            eapply IH.
          }
        }
        { (* input data is not nil *)
          intros b l bl_eq.
          case_eq (word_eq word_zero (callenv_value callenv)).
          { (* sent value is zero *)
            intro sent_zero.
            (* hmmm wanting ssreflect tactics. *)
            match goal with
              | [ |- ((if ?t then _ else _) = _) -> _] => case_eq t
            end.
            {
              intro data_big_enough.
              unfold sending_action.
              (* Here, before introducing the existential variables,
               * all ambuiguities must be resolved. *)
              set (enough_balance_spec := word_smaller_or_eq _ _).
              case_eq enough_balance_spec.
              { (* enough balance *)
                intro enough_balance_spec_t.
                intro H.
                inversion H; subst.
                clear H.
                eexists.
                eexists.
                eexists.
                split.
                {
                  intro s.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  cbn.
                  assert (Q : word_smaller 13%Z 256%Z = true) by admit.
                  rewrite Q.
                  cbn.
                  unfold datasize.
                  cbn.
                  set (e0 := ZModulo.eq0 _ _).
                  assert (R : e0 = false) by admit.
                  rewrite R.
                  unfold N_of_word.
                  cbn.
                  unfold ZModulo.to_Z.
                  unfold ZModulo.wB.
                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  simpl.
                  assert (Z : word_iszero (callenv_value callenv) = true) by admit.
                  rewrite Z.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  cbn.
                  set (ws := word_smaller 64%Z 256%Z).
                  compute in ws.
                  unfold ws.
                  clear ws.
                  cbn.
                  unfold datasize.
                  simpl.
                  set (s64 := word_smaller _ _).
                  assert (S : s64 = false) by admit.
                  rewrite S.
                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  cbn.
                  (** TODO: make this tactic only when immediate *)
                  (** TODO: use this tactic *)
                  Ltac compute_word_smaller :=
                    set (focus := word_smaller _ _);
                    compute in focus;
                    unfold focus;
                    clear focus.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  set (balance_smaller := word_smaller _ _).
                  assert (F : balance_smaller = false)by admit (* use enough_balance_spec *).
                  rewrite F.
                  clear F.
                  right.
                  f_equal.
                  f_equal.
                  f_equal.
                  {
                    unfold cut_data.
                    simpl.
                    rewrite bl_eq.
                    reflexivity.
                  }
                  {
                    unfold cut_data.
                    simpl.
                    rewrite bl_eq.
                    reflexivity.
                  }
                  {
                    unfold cut_data.
                    simpl.
                    rewrite bl_eq.
                    reflexivity.
                  }
                  {
                    (* TODO: need to define cut_memory *)
                    admit.
                  }
                }
                {
                  cbn.
                  unfold cut_data.
                  cbn.
                  (* spec says nil, but actually a call is pushed *)
                  admit.
                }
              }
              { (* not enough balance *)
                intro not_enough_spec.
                intro H.
                inversion H; subst.
                clear H.

                eexists.
                eexists.
                eexists.
                split.
                {
                  intro s.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  cbn.
                  assert (Q : word_smaller 13%Z 256%Z = true) by admit.
                  rewrite Q.
                  cbn.
                  unfold datasize.
                  cbn.
                  set (e0 := ZModulo.eq0 _ _).
                  assert (R : e0 = false) by admit.
                  rewrite R.
                  unfold N_of_word.
                  cbn.
                  unfold ZModulo.to_Z.
                  unfold ZModulo.wB.
                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  simpl.
                  assert (Z : word_iszero (callenv_value callenv) = true) by admit.
                  rewrite Z.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  cbn.
                  set (ws := word_smaller 64%Z 256%Z).
                  compute in ws.
                  unfold ws.
                  clear ws.
                  cbn.
                  unfold datasize.
                  simpl.
                  set (s64 := word_smaller _ _).
                  assert (S : s64 = false) by admit.
                  rewrite S.
                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  compute_word_smaller; cbn.
                  set (cd := cut_data _ _).
                  (* TODO: cut_data needs to be defined *)
                  assert (cdH : cd = list_slice 0 32 (callenv_data callenv)) by admit.
                  rewrite cdH.
                  clear cdH cd.
                  set (balance_smaller := word_smaller _ _).
                  assert (A : balance_smaller = true) by admit.
                  rewrite A.
                  right.
                  eauto.
                }
                {

                  (* This one should be now ready *)
                  admit.
                }
              }
            }
            {
              intro data_short.
              unfold failing_action.
              intro H.
              inversion H; subst.
              clear H.
              eexists.
              eexists.
              eexists.
              split.
              {
                intros s.
                repeat (case s as [| s]; [ solve [left; auto] | ]).
                cbn.
                unfold plus_size_label.
                assert (E : word_smaller 13%Z 256%Z = true).
                {
                  compute; auto.
                }
                rewrite E.
                cbn.
                unfold datasize.
                set (zero_cond := ZModulo.eq0 _ _ ).
                assert (Zf : zero_cond = false) by admit.
                rewrite Zf.
                (* something wrong is happening, so this should contradict? *)


                admit.
              }
              {
                (* need to solve the previous goal first *)
                admit.
              }
            }
          }
          { (* sent value is not zero *)
            (* I can just imagine this needs the definition of datasize, too *)
            admit.
          }
        }
      }
    }
    {
      (* this does not make sense until the call stack is non-empty *)
      admit.
    }
    {
      (* this does not make sense until the call stack is non-empty *)
      admit.
    }
  Admitted.

End ExamplesOnConcreteWord.

(* TODO: currently,
   lack of balance is treated in the semantics, but lack of gas is not.
   This discrepancy needs to be solved.
*)
