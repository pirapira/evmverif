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
Lemma addsub :
  forall x y z,
    ZModulo.add (ZModulo.sub x y) z =
    ZModulo.sub (ZModulo.add x z) y.
Proof.
  unfold ZModulo.add.
  unfold ZModulo.sub.
  intros ? ? ?.
  omega.
Qed.


Lemma addK :
  forall a b, ZModulo.sub (ZModulo.add a b) b = a.
Proof.
  unfold ZModulo.add.
  unfold ZModulo.sub.
  intros ? ?; omega.
Qed.

Lemma addC (* This lemma should not enter Word. *) :
  forall a b, ZModulo.add a b = ZModulo.add b a.
Proof.
  unfold ZModulo.add.
  intros ? ?; omega.
Qed.

Require ConcreteWord.

Module ExamplesOnConcreteWord.

  Module ConcreteSem := (ContractSem.Make ConcreteWord.ConcreteWord).
  Include ConcreteSem.

  (** TODO: make this tactic only when immediate *)
  (** TODO: use this tactic *)
  Ltac compute_word_smaller :=
    set (focus := word_smaller _ _);
    compute in focus;
    unfold focus;
    clear focus.


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


  (* TODO:
     this has to remember the states in the stack as well *)
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
        failing_action (counter_wallet income_sofar spending_sofar
                       (* TODO: this is wrong, this has to be taken from the storage *) )
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
    intros i s.
    unfold counter_wallet.
    apply response_expander_eq.
  Qed.

  (* TODO: streamline this by allowing labels in JUMPDEST *)
  Definition plus_size_label : word := 13%Z.
  Arguments plus_size_label /.

  (* TODO: add owner as an immediate value and check it *)
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

  Record counter_wallet_calling_state (v : variable_env) : Prop :=
    {
      cw_calling_income_sofar : word;
      cw_calling_spending_sofar : word;
      cw_calling_prg_sfx :
        (v.(venv_prg_sfx) =
         ISZERO ::
             PUSH1 word_zero ::
             JUMPI ::
             STOP ::
             nil) ;
      cw_calling_balance :
        venv_balance_at_call v counter_wallet_address =
        word_sub cw_calling_income_sofar cw_calling_spending_sofar
    }.

  Definition all_cw_calling_state lst :=
    forall v, In v lst -> counter_wallet_calling_state v.

  Lemma all_cw_calling_state_head_tail :
    forall head tail,
      all_cw_calling_state (head :: tail) ->
      all_cw_calling_state tail /\ counter_wallet_calling_state head.
  Proof.
    intros head tail H.
    split.
    {
      intro elm.
      intro elmh.
      apply H.
      apply in_cons.
      auto.
    }
    apply H.
    apply in_eq.
  Qed.

  Theorem counter_wallet_correct :
    forall (income_sofar spending_sofar : word) ongoing,
      all_cw_calling_state ongoing ->
      account_state_responds_to_world
        (counter_wallet_account_state income_sofar spending_sofar ongoing)
        (counter_wallet income_sofar spending_sofar)
        counter_wallet_invariant.
    (* TODO: strengthen the statement so that coinduction goes through. *)
  Proof.
    cofix.
    intros income_sofar spending_sofar ongoing ongoingH.
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
            repeat (case s as [| s]; [ solve [left; auto] | cbn ]).
            rewrite data_nil.
            repeat (case s as [| s]; [ solve [left; auto] | cbn ]).
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
            rewrite address_eq_refl.
            rewrite addsub.
            eapply IH.
            assumption.
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
                  unfold datasize.
                  cbn.
                  set (s64 := word_smaller _ _).
                  assert (S : s64 = false) by admit.
                  rewrite S.
                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | cbn ]).
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
                  unfold counter_wallet_account_state in counter_wallet_correct.
                  set (new_storage := storage_store _ _ _).
                  set (new_ongoing := _ :: ongoing).
                  unfold update_balance.
                  rewrite address_eq_refl.
                  set (new_balance := if (_ : bool) then _ else _).
                  set (new_sp := ZModulo.add spending_sofar _).
                  assert (S : new_storage = counter_wallet_storage income_sofar new_sp) by admit.
                  rewrite S.
                  assert (B : new_balance = word_sub income_sofar new_sp) by admit.
                  rewrite B.
                  apply (counter_wallet_correct income_sofar new_sp).
                  unfold new_ongoing.
                  unfold all_cw_calling_state.
                  intros elm elmH.
                  apply in_inv in elmH.
                  case elmH.
                  {
                    intro K.
                    rewrite <-K.
                    apply (Build_counter_wallet_calling_state _ income_sofar spending_sofar).
                    { reflexivity. }
                    {
                      cbn.
                      rewrite get_update_balance.
                      reflexivity.
                    }
                  }
                  {
                    apply ongoingH.
                  }
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
                  unfold datasize.
                  simpl.
                  set (s64 := word_smaller _ _).
                  assert (S : s64 = false) by admit.
                  rewrite S.
                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | cbn ]).
                  set (cd := cut_data _ _).
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
                  simpl.
                  unfold counter_wallet_account_state in counter_wallet_correct.
                  unfold update_balance.
                  rewrite address_eq_refl.
                  apply counter_wallet_correct.
                  assumption.
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
                repeat (case s as [| s]; [ solve [left; auto] | cbn ]).
                unfold plus_size_label.
                unfold datasize.
                cbn.
                set (zero_cond := ZModulo.eq0 _ _ ).
                assert (Zf : zero_cond = false) by admit.
                rewrite Zf.
                cbn.
                simpl.
                repeat (case s as [| s]; [ solve [left; auto] | ]).
                cbn.
                set (z_cond := ZModulo.eq0 _ _).
                assert (Zt : z_cond = true) by admit.
                rewrite Zt.
                repeat (case s as [| s]; [ solve [left; auto] | ]).
                cbn.
                unfold datasize.
                cbn.
                set (small := word_smaller _ _).
                assert (SS : small = true) by admit.
                rewrite SS.
                simpl.
                right.
                eauto.
              }
              {
                unfold update_account_state.
                cbn.
                unfold update_balance.
                rewrite address_eq_refl.
                apply counter_wallet_correct.
                assumption.
              }
            }
          }
          { (* sent value is not zero, and data is also sent; should fail *)
            (* I can just imagine this needs the definition of datasize, too *)
            idtac.
            intro value_nonzero.
            intro H.
            inversion H; subst.
            eexists.
            eexists.
            eexists.
            split.
            {
              intro s.
              repeat (case s as [| s]; [ solve [left; auto] | ]).
              cbn.
              unfold datasize.
              cbn.
              set (e0 := ZModulo.eq0 _ _).
              assert (E0 : e0 = false) by admit (* an extra assumption that data is not as long as 2^256 is needed*).
              rewrite E0.
              simpl.
              (* TODO: define a lemma so that just proving something for a large s is enough *)
              repeat (case s as [| s]; [ solve [left; auto] | ]).
              cbn.
              set (v0 := ZModulo.eq0 _ _).
              assert (V0 : v0 = false) by admit.
              rewrite V0.
              cbn.
              right. (* TODO: maybe name a constructor *)
              eauto.
            }
            {
                unfold update_account_state.
                cbn.
                unfold update_balance.
                rewrite address_eq_refl.
                apply counter_wallet_correct.
                assumption.
            }
          }
        }
      }
    }
    {
      (* Now this goal does make sense *)
      (* TODO: maybe try to see the required condition here? *)
      unfold respond_to_return_correctly.
      intros rr venv cont act.
      intro venvH.
      intro H.
      inversion H; subst.
      clear H.
      unfold build_venv_returned in venvH.
      unfold counter_wallet_account_state in venvH.
      cbn in venvH.
      case ongoing as [| recovered rest_oging]; try congruence.
      (* TODO: define a property that implies this goal *)
      eexists.
      eexists.
      eexists.
      split.
      {
        inversion venvH; subst.
        clear venvH.
        unfold all_cw_calling_state in ongoingH.
        assert (CSR : counter_wallet_calling_state recovered)
          by (* TODO: use all_cw_calling_state *) admit.
        rewrite (cw_calling_prg_sfx _ CSR).
        intro s.
        repeat (case s as [| s]; [ solve [left; auto] | ]).
        simpl.
        right.
        f_equal.
        }
      {
        unfold update_account_state.
        unfold counter_wallet_account_state in counter_wallet_correct.
        unfold account_state_update_storage.
        simpl.

        rewrite get_update_balance.
        apply counter_wallet_correct.


        apply all_cw_calling_state_head_tail in ongoingH.
        tauto.
      }
    }
    {
      unfold respond_to_fail_correctly.
      intros v c a.
      intro v_eq.
      intro a_c_eq.
      inversion a_c_eq; subst.
      unfold failing_action in a_c_eq.
      clear a_c_eq.
      unfold build_venv_fail in v_eq.
      simpl in v_eq.
      case_eq ongoing.
      {
        intros ?.
        subst.
        congruence.
      }
      intros ongoing_head ongoing_tail ongoing_eq.
      subst.
      inversion v_eq; subst.
      clear v_eq.
      apply all_cw_calling_state_head_tail in ongoingH.
      case ongoingH as [ongoing_tailH ongoing_headH].

      eexists.
      eexists.
      eexists.
      split.
      {
        intro s.
        case ongoing_headH.
        clear ongoing_headH.
        intros orig_income_sofar orig_spending_sofar ongoing_head_sfx_eq balance_eq.
        rewrite ongoing_head_sfx_eq.

        repeat (case s as [| s]; [ solve [left; auto] | cbn ]).

        assert (Q : ZModulo.eq0 ALEN.p ZModulo.one = false) by admit.
        rewrite Q.
        simpl.
        right.
        reflexivity.
      }
      { (* somehow use the induction hypothesis *)
        idtac.

        unfold update_account_state.
        cbn.
        case ongoing_headH.
        clear ongoing_headH.
        intros orig_income orig_spending sfx_eq balance_eq.

        generalize (counter_wallet_correct orig_income orig_spending ongoing_tail ongoing_tailH).
        unfold counter_wallet_account_state.
        assert (S : venv_storage_at_call ongoing_head = counter_wallet_storage orig_income orig_spending).
        {
          admit.
        }
        rewrite S.
        rewrite balance_eq.

        (* the specification must be fixed first *)
        admit.
      }
    }
  Admitted.

End ExamplesOnConcreteWord.

(* TODO: currently,
   lack of balance is treated in the semantics, but lack of gas is not.
   This discrepancy needs to be solved.
*)
