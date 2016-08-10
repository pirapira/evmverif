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
      (fun retval => ContractAction (ContractReturn retval.(return_data)) (call_but_fail_on_reentrance O))
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
          assert (H : word_mod (word_of_N 0) (word_of_N 256) = word_of_N 0) by admit.
          rewrite H.
          simpl.
          auto.
          simpl.
          rewrite N_of_word_of_N.
          { cbn.
            right.
            eauto.
          }
          compute.
          auto.
        }
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
  Admitted.

End Example0Continue.


Section Example1Continue.
(*** prove that example 1 has an implementation  *)

  Definition return_result_nil : list byte := nil.
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
        assert (Z : word_mod word_zero (word_of_N 256) = word_zero).
        {
          admit.
        }
        case steps as [|steps]; [left; auto | ].
        case steps as [|steps]; [left; auto | ].
        case steps as [|steps]; [left; auto | ].
        unfold action_example_1 in H.
        always_return_tac.
        right.
        simpl.
        f_equal.
        f_equal.
        simpl.
        rewrite Z.
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
  Admitted.

End Example1Continue.

End AbstractExamples.
