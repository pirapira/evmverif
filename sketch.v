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
  (* TODO:
     why can't this be computed from the bytecode easily...
     which is called the static symbolic execution... *)
  CoFixpoint counter_wallet (income_sofar : word) (spending_sofar : word)
             (stack : list (word * word))
    : response_to_world :=
    Respond
      (fun cenv =>
         match word_eq word_zero (word_of_nat (length (callenv_data cenv))) with
         | true => receive_eth (counter_wallet (word_add income_sofar cenv.(callenv_value)) spending_sofar stack)
         | false =>
           if word_eq word_zero (cenv.(callenv_value)) then
             if word_smaller (word_of_nat (List.length cenv.(callenv_data))) 64%Z then
               failing_action (counter_wallet income_sofar spending_sofar stack)
             else
               let addr := list_slice 0 32 cenv.(callenv_data) in
               let value := list_slice 32 32 cenv.(callenv_data) in
               if word_smaller (word_sub (word_add income_sofar cenv.(callenv_value)) spending_sofar) value then
                 failing_action
                   (counter_wallet income_sofar spending_sofar stack)
               else
                 sending_action addr value
                                (counter_wallet income_sofar (word_add spending_sofar value)
                                                ((income_sofar, spending_sofar) :: stack))
           else
             failing_action (counter_wallet income_sofar spending_sofar stack)
         end
      )
      (fun returned =>
         match stack with
         | _ :: new_stack =>
             ContractAction (ContractReturn nil)
                            (counter_wallet income_sofar spending_sofar new_stack)
         | nil =>
           failing_action (counter_wallet income_sofar spending_sofar stack)
         end
      )
      (
        match stack with
        | (income_old, spending_old) :: new_stack =>
          failing_action (counter_wallet income_old spending_old new_stack)
        | nil =>
          failing_action (counter_wallet income_sofar spending_sofar stack)
        end
      )
      .

  Lemma counter_wallet_def :
    forall income_sofar spending_sofar stack,
      counter_wallet income_sofar spending_sofar stack =
    Respond
      (fun cenv =>
         match word_eq word_zero (word_of_nat (length (callenv_data cenv))) with
         | true => receive_eth (counter_wallet (word_add income_sofar cenv.(callenv_value)) spending_sofar stack)
         | false =>
           if word_eq word_zero (cenv.(callenv_value)) then
             if word_smaller (word_of_nat (List.length cenv.(callenv_data))) 64%Z then
               failing_action (counter_wallet income_sofar spending_sofar stack)
             else
               let addr := list_slice 0 32 cenv.(callenv_data) in
               let value := list_slice 32 32 cenv.(callenv_data) in
               if word_smaller (word_sub (word_add income_sofar cenv.(callenv_value)) spending_sofar) value then
                 failing_action
                   (counter_wallet income_sofar spending_sofar stack)
               else
                 sending_action addr value
                                (counter_wallet income_sofar (word_add spending_sofar value)
                                                ((income_sofar, spending_sofar) :: stack))
           else
             failing_action (counter_wallet income_sofar spending_sofar stack)
         end
      )
      (fun returned =>
         match stack with
         | _ :: new_stack =>
             ContractAction (ContractReturn nil)
                            (counter_wallet income_sofar spending_sofar new_stack)
         | nil =>
           failing_action (counter_wallet income_sofar spending_sofar stack)
         end
      )
      (
        match stack with
        | (income_old, spending_old) :: new_stack =>
          failing_action (counter_wallet income_old spending_old new_stack)
        | nil =>
          failing_action (counter_wallet income_sofar spending_sofar stack)
        end
      )
      .
  Proof.
    intros i s stack.
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

  Record counter_wallet_calling_state (income_for_reset : word) (spending_for_reset : word) (v : variable_env) : Prop :=
    {
      cw_calling_prg_sfx :
        (v.(venv_prg_sfx) =
         ISZERO ::
             PUSH1 word_zero ::
             JUMPI ::
             STOP ::
             nil) ;
      cw_calling_balance :
        venv_balance_at_call v counter_wallet_address =
        word_sub income_for_reset spending_for_reset ;
      cw_calling_storage :
        v.(venv_storage_at_call) =
         counter_wallet_storage income_for_reset spending_for_reset
    }.

  (* TODO: define this *)
  Inductive all_cw_corresponds :
            list variable_env -> list (word * word) -> Prop :=
  | acc_nil : all_cw_corresponds nil nil
  | acc_cons :
      forall hd_venv tail_venvs hd_income hd_spending tail_stack,
        counter_wallet_calling_state hd_income hd_spending hd_venv ->
        all_cw_corresponds tail_venvs tail_stack ->
        all_cw_corresponds (hd_venv :: tail_venvs)
                         ((hd_income, hd_spending) :: tail_stack)
  .

  Lemma find_remove :
    forall a b orig,
      ST.find (elt:=word) a (ST.remove b orig) =
      if (word_eq a b) then None
      else ST.find (elt := word) a orig.
  Proof.
    intros a b orig.
    admit.
  Admitted.

  Lemma find_add :
    forall a b c orig,
      ST.find (elt:=word) a (ST.add b c orig) =
      if (word_eq a b) then Some c
      else ST.find (elt := word) a orig.
  Proof.
    intros a b c orig.
    admit.
  Admitted.

  Lemma storage_load_store :
    forall r w x orig,
      storage_load r (storage_store w x orig) =
      if word_eq r w then x else storage_load r orig.
  Proof.
    intros r w x orig.
    unfold storage_load.
    unfold storage_store.
    case_eq (word_eq word_zero x).
    {
      intro x_zero.
      case_eq (word_eq r w).
      { (* r is w *)
        intro rw.
        assert (H : r = w) by admit.
        subst.
        set (found := ST.find _ _).
        assert (H : found = None) by admit.
        rewrite H.
        (* use x_zero; a lemma for concrete word is needed *)
        admit.
      }
      {
        (* r is not w *)
        intro rw.
        (* move this lemma somewhere in the library *)
        rewrite find_remove.
        rewrite rw.
        reflexivity.
      }
    }
    {
      (* x is not zero *)
      intro x_not_zero.
      rewrite find_add.
      set (e := word_eq _ _).
      case_eq e; try solve [auto].
    }
  Admitted.

  Theorem counter_wallet_correct :
    forall (income_sofar spending_sofar : word) ongoing stack,
      all_cw_corresponds ongoing stack ->
      account_state_responds_to_world
        (counter_wallet_account_state income_sofar spending_sofar ongoing)
        (counter_wallet income_sofar spending_sofar stack)
        counter_wallet_invariant.
    (* TODO: strengthen the statement so that coinduction goes through. *)
  Proof.
    cofix.
    intros income_sofar spending_sofar ongoing stack ongoingH.
    rewrite counter_wallet_def.
    apply AccountStep.
    {
      unfold respond_to_call_correctly.
      intros callenv act cont.
      split.
      {
        unfold counter_wallet_invariant.
        cbn.
        unfold update_balance.
        rewrite address_eq_refl.
        unfold counter_wallet_storage.
        set (spend := storage_load 1%Z _).
        (* TODO: a geneeral lemma is needed here *)
        assert (spendH : spend = spending_sofar).
        {
          unfold spend.
          clear spend.
          rewrite storage_load_store.
          rewrite ST.E.eq_refl.
          reflexivity.
        }
        rewrite spendH.
        set (income := storage_load 0%Z _).
        assert (incomeH : income = income_sofar).
        {
          unfold income.
          rewrite storage_load_store.
          set (e := word_eq _ _).
          compute in e.
          unfold e.
          clear e.
          rewrite storage_load_store.
          set (e := word_eq _ _).
          compute in e.
          unfold e.
          reflexivity.
        }
        rewrite incomeH.
        generalize word_add_sub.
        cbn.
        intro was.
        rewrite !was.
        generalize word_addK.
        intro wK.
        cbn in wK.
        rewrite wK.
        apply word_addC.
      }
      {
        intro I.
        set (data_len_zero := word_eq word_zero (word_of_nat _)).
        case_eq data_len_zero.
        { (* data_len_is_zero *)
          intro data_len_is_zero.
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
            unfold datasize.
            cbn.
            unfold word_iszero.
            rewrite data_len_is_zero.
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
            set (new_income := ZModulo.to_Z _ (ZModulo.add income_sofar _)).
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
            generalize word_add_sub.
            cbn.
            intro was.
            rewrite was.
            cbn in IH.
            clear II.
            clear was.
            
            eapply IH.
            assumption.
          }
        }
        { (* input data is not nil *)
          intros data_len_non_zero.
          case_eq (word_eq word_zero (callenv_value callenv)).
          { (* sent value is zero *)
            intro sent_zero.
            (* hmmm wanting ssreflect tactics. *)
            match goal with
              | [ |- ((if ?t then _ else _) = _) -> _] => case_eq t
            end.
            
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
                set (zero_cond := word_iszero _ ).
                assert (Zf : zero_cond = false) by assumption.
                rewrite Zf.
                cbn.
                simpl.
                repeat (case s as [| s]; [ solve [left; auto] | ]).
                cbn.
                set (z_cond := word_iszero _).
                assert (Zt : z_cond = true) by assumption.
                rewrite Zt.
                repeat (case s as [| s]; [ solve [left; auto] | ]).
                cbn.
                unfold datasize.
                cbn.
                set (small := word_smaller _ _).
                assert (SS : small = true).
                {
                  unfold small.
                  assumption.
                }
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
            {
              intro data_big_enough.
              unfold sending_action.
              (* Here, before introducing the existential variables,
               * all ambuiguities must be resolved. *)
              set (enough_balance_spec := word_smaller _ _).
              case_eq enough_balance_spec.
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
                  set (e0 := word_iszero _).
                  assert (R : e0 = false) by admit.
                  rewrite R.
                  unfold N_of_word.
                  cbn.
                  set (matched := Z.to_N (ZModulo.to_Z _ (ZModulo.modulo _ 13 256))).
                  compute in matched.
                  unfold matched.
                  clear matched.                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  simpl.
                  assert (Z : word_iszero (callenv_value callenv) = true)
                  by assumption.
                  rewrite Z.
                  repeat (case s as [| s]; [ solve [left; auto] | ]).
                  cbn.
                  unfold datasize.
                  simpl.
                  set (s64 := word_smaller _ _).
                  assert (S : s64 = false).
                  {
                    unfold s64.
                    set (x := ZModulo.modulo _ _ _ ).
                    compute in x.
                    unfold x.
                    (* TODO: the use of nat in data_big_enough is not good *)
                    admit.
                  }

                  rewrite S.
                  simpl.
                  repeat (case s as [| s]; [ solve [left; auto] | cbn ]).
                  set (cd := cut_data _ _).
                  assert (cdH : cd = list_slice 32 32 (callenv_data callenv)).
                  {
                    unfold cd.
                    cbn.
                    (* TODO: define cut_data *)
                    admit.
                  }
                  rewrite cdH.
                  clear cdH cd.
                  set (balance_smaller := word_smaller _ _).
                  assert (A : balance_smaller = true).
                  {
                    unfold balance_smaller.
                    rewrite get_update_balance.
                    generalize word_add_sub.
                    cbn.
                    intro K.
                    rewrite K.
                    assumption.
                  }
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
                  set (e0 := word_iszero _).
                  assert (R : e0 = false) by admit.
                  rewrite R.
                  unfold N_of_word.
                  cbn.
                  set (matched := Z.to_N (ZModulo.to_Z _ (ZModulo.modulo _ 13 256))).
                  compute in matched.
                  unfold matched.
                  clear matched.                  simpl.
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
                  cbn.
                  right.
                  f_equal.
                  f_equal.
                  f_equal.
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
                  (* already ZModulo.add (ZModulo.sub *)

                  unfold update_balance.
                  rewrite address_eq_refl.

                  set (new_balance := if (_ : bool) then _ else _).

                  set (new_sp := ZModulo.to_Z _ (ZModulo.add spending_sofar _)).
                  assert (S : new_storage = counter_wallet_storage income_sofar new_sp).
                  {
                    unfold new_storage.
                    admit.
                  }

                  rewrite S.
                  assert (B : new_balance = word_sub income_sofar new_sp).
                  {
                    clear ongoing ongoingH I new_ongoing.
                    set (self := address_eq _ _) in new_balance.
                    case_eq self.
                    {
                      (* the receiver is the self, easier case *)
                      intro selfT.
                      unfold new_balance.
                      rewrite selfT.
                      unfold new_sp.
                      generalize word_add_zero.
                      intro T.
                      cbn in T.
                      rewrite (T _ _ sent_zero).
                      generalize word_sub_sub.
                      clear S.
                      intro S.
                      cbn in S.
                      cbn.
                      rewrite !S.
                      Lemma modulo_idem :
                        forall a,
                          ZModulo.to_Z ALEN.p (ZModulo.to_Z ALEN.p a) =
                          ZModulo.to_Z ALEN.p a.
                      Proof.
                      Admitted.
                      rewrite modulo_idem.
                      generalize word_add_sub.
                      intro K.
                      cbn in K.
                      rewrite K.
                      clear new_balance.
                      clear T S K.
                      clear selfT.
                      set (c := N_of_word _).
                      compute in c.
                      unfold c.
                      clear c.
                      generalize word_sub_sub.
                      intro S.
                      cbn in S.
                      cbn.
                      rewrite <- !S.

                      (* TODO: investigate why this case analysis
                       * happens at all *)
                      (* RHS is wrong.  In this case the balance should not change *)
                      admit.
                    }
                    {
                      intro selfF.
                      unfold new_balance.
                      rewrite selfF.
                      clear new_balance.
                      unfold new_sp.
                      generalize word_add_sub.
                      intro K.
                      cbn in K.
                      rewrite K.
                      clear K.
                      clear S.
                      clear new_storage.
                      generalize word_add_zero.
                      intro S.
                      cbn in S.
                      rewrite S by assumption.
                      (* this is a bit awkward,
                       * maybe the statement should be simplified *)
                      generalize word_sub_sub.
                      clear S.
                      intro S.
                      cbn in S.
                      cbn.
                      rewrite !S.
                      f_equal.
                      rewrite word_sub_modulo.
                      f_equal.
                    }
                  }
                  rewrite B.
                  apply (counter_wallet_correct income_sofar new_sp).

                  unfold new_ongoing.
                  apply acc_cons.
                  {
                    simpl.
                    refine (
                        {|
                          cw_calling_prg_sfx := _ ;
                          cw_calling_balance := _
                        |}
                      ).
                    {
                      reflexivity.
                    }
                    {
                      cbn.
                      rewrite get_update_balance.
                      reflexivity.
                    }
                    {
                      cbn.
                      reflexivity.
                    }
                  }
                  {
                    assumption.
                  }
                }
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
              set (e0 := word_iszero _).
              assert (E0 : e0 = false).
              {
                assumption.
              }
              rewrite E0.
              simpl.
              (* TODO: define a lemma so that just proving something for a large s is enough *)
              repeat (case s as [| s]; [ solve [left; auto] | ]).
              cbn.
              set (v0 := word_iszero _).
              assert (V0 : v0 = false).
              {
                (* maybe this should be a lemma *)
                unfold v0.
                generalize value_nonzero.
                unfold word_eq.
                unfold ZModulo.eq0.
                set (v := callenv_value _).
                case_eq v; auto.
              }
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
      case ongoing as [| recovered rest_ongoing]; try congruence.
      inversion ongoingH; subst.
      (* I don't like the generated names... *)
      (* TODO: create a theorem instead of inversion ongoingH *)

      case H2.
      clear H2.
      intros sfx_eq bal_eq.
      inversion H1; subst.


      (* TODO: define a property that implies this goal *)
      eexists.
      eexists.
      eexists.
      split.
      {
        inversion venvH; subst.
        clear venvH.
        rewrite sfx_eq.

        intro s.
        repeat (case s as [| s]; [ solve [left; auto] | cbn ]).
        simpl.
        right.
        eauto.
      }
      {
        unfold update_account_state.
        unfold counter_wallet_account_state in counter_wallet_correct.
        unfold account_state_update_storage.
        simpl.

        rewrite get_update_balance.
        apply (counter_wallet_correct income_sofar spending_sofar
                                           rest_ongoing tail_stack).
        assumption.
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
      inversion ongoingH; subst.
      clear ongoingH.
      inversion H0; subst.
      (* TODO: replace these lines with something new.
      apply all_cw_calling_state_head_tail in ongoingH.
      case ongoingH as [ongoing_tailH ongoing_headH]. *)

      eexists.
      eexists.
      eexists.
      split.
      {
        intro s.
        case H2.
        clear H2.
        intros ongoing_head_sfx_eq balance_eq storage_eq.
        rewrite ongoing_head_sfx_eq.

        repeat (case s as [| s]; [ solve [left; auto] | cbn ]).

        assert (Q : word_iszero (ZModulo.to_Z ALEN.p ZModulo.one) = false).
        {
          compute.
          auto.
        }
        rewrite Q.
        simpl.
        right.
        eauto.
      }
      { (* somehow use the induction hypothesis *)
        unfold update_account_state.
        cbn.

        generalize (counter_wallet_correct hd_income hd_spending
                                           ongoing_tail tail_stack).
        unfold counter_wallet_account_state.
        case H2; clear H2.
        intros sfx_eq balance_eq storage_eq.
        rewrite storage_eq.
        rewrite balance_eq.
        tauto.
      }
    }
  Admitted.

End ExamplesOnConcreteWord.

(* TODO: currently,
   lack of balance is treated in the semantics, but lack of gas is not.
   This discrepancy needs to be solved.
*)
