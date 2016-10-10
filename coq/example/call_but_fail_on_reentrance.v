Require Import ContractSem.
Require Import ConcreteWord.
Require Import ZArith.


Module ConcreteSem := (ContractSem.Make ConcreteWord.ConcreteWord).
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
  unfold example2_spec.
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
    rewrite call_but_fail_on_reentrace_0_eq.
    apply AccountStep.
    {
      unfold respond_to_call_correctly.
      intros ce a con.
      split; [ solve [auto] | ].
      intros _ next.
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
      compute_word_mod.
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
      inversion next; subst.
      clear next.
      eexists.
      eexists.
      eexists.
      split; try reflexivity.
      simpl.
(*      rewrite <- contract_action_expander_eq in next at 1. *)

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
        intro s.
        repeat (case s as [| s]; [ solve [left; auto] | ]).
        simpl.
        rewrite st_code.
        unfold example2_program.
        cbn.
        repeat (case s as [| s]; [ solve [left; auto] | ]).
        cbn.
        rewrite st_load.
        simpl.
        rewrite st_code.
        simpl.
        right.
        eexists.
        eexists.
        eexists.
        split; [ solve [eauto] | ].
        unfold build_venv_called.
        cbn.
        apply example2_spec_impl_match.
        unfold example2_depth_n_state.
        intuition.
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
      intros act_cont_eq.
      intro s.
      rewrite prevH''.
      repeat (case s as [| s]; [ solve [left; auto] | ]).
      simpl.
      right.
      f_equal.
      inversion act_cont_eq; subst.

      eexists.
      eexists.
      eexists.
      split; [reflexivity | ].
      inversion act_cont_eq; subst.
      apply example2_spec_impl_match.
      unfold example2_depth_n_state.
      left.
      repeat (split; auto); tauto.
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
      intros act_cont_H.
      inversion act_cont_H; subst.
      clear act_cont_H.
      intro s.
      rewrite ve_sfx.
      repeat (case s as [| s]; [ solve [left; auto] | ]).
      simpl.
      rewrite st_code.
      simpl.
      right.
      f_equal.
      eexists.
      eexists.
      eexists.
      split; [reflexivity | ].
      simpl.
      apply example2_spec_impl_match.
      unfold example2_depth_n_state.
      left.
      repeat split; auto; tauto.
    }
  }
Qed.
