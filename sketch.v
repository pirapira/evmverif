(* EVM Contract Behavior Formalization *)
(* for Coq 8.5pl1 *)

(* Yoichi Hirai i@yoichihirai.com
   Creative Commons Attribution-ShareAlike 4.0 International License *)

(* This is just a sketch of an idea. *)
(* Gas is not considered among many things.  A contract in reality dies more often than described here. *)


(***
 *** Some basic <del>definitions</del> assumptions
 ***)

(* Here I'm being lazy and assuming that these things exist.
 * I hope these don't enable us to prove 0 = 1.
 *)
Axiom word  : Set.      (* Does anyone know a good uint256 library for Coq? *)
Axiom word_add : word -> word -> word.
Axiom word_sub : word -> word -> word.
Axiom word_one : word.
Axiom word_zero : word.
Axiom word_iszero : word -> bool.
Axiom word_smaller : word -> word -> bool.

Definition bool_to_word (b : bool) :=
  if b then word_one else word_zero.

Axiom byte : Set.
Axiom address : Set.
Axiom address_of_word : word -> address.

Axiom event : Set. (* logged events *)

Open Scope list_scope.

Definition drop_one_element {A : Type} (lst : list A) :=
  match lst with
  | nil => nil
  | _ :: tl => tl
  end.

(***
 *** Some abstract view over EVM
 ***)

(** This part is hugely incomplete.  It misses many instructions and
    gas economy.  They will be added as necessary. *)

(* An element of type [call_arguments] describes
   arguments that an execution can attach to
   [CALL] *)
Record call_arguments :=
    { callarg_gaslimit    : word
    ; callarg_code        : address
    ; callarg_recipient   : address
    ; callarg_value       : word
    ; callarg_data        : list byte
    ; callarg_output_begin : word
    ; callarg_output_size : word
    }.

(* An element of type [return_result] is a sequence of bytes that
   [RETURN] can return. *)
Definition return_result := list byte.

(* An element of type [call_env] describes
   an environment where contract is executed
 *)
Record call_env :=
  { callenv_gaslimit : word
  ; callenv_value : word
  ; callenv_data : list byte
  ; callenv_caller : address
  ; callenv_timestap : word
  ; callenv_blocknum : word
  ; callenv_balance : address -> word
  }.


Inductive contract_action :=
| ContractCall : call_arguments -> contract_action
  (* [Call args continuation] is the behavior of [CALL] instruction
      together with all behaviors shown by the account after the [CALL].
     [args] represents the parameters of a call.
     [continuation] represents the behavior shown after the [CALL]
     instruction.  See the comment at [after_call_behavior].
   *)
| ContractFail : contract_action
  (* [Fail] is the behavior of runtime errors (e.g. jumping to an invalid
     program counter / lack of gas *)
| ContractSuicide : contract_action
| ContractReturn : return_result (* returned data *) -> contract_action.
  (* [Return ret next] is the behavior of a [RETURN], [STOP] instruction.
     Upon the next call with [env], [next env] will be the contract behavior.
   *)


(* An element of type [responce_to_world] describes a strategy of a contract
   that can respond when
   1. it is called from the world
   2. it receives a callee return from the world
   3. it receives a callee failure from the world.
   Initially, when the contract has not called any other accounts,
   the points 2. and 3. are useless.
 *)
CoInductive responce_to_world :=
| Respond :
    (call_env -> contract_behavior) (* what to do if called / or re-entered *) ->
    (return_result -> contract_behavior) (* what to do if the callee returns (if exists) *) ->
    (contract_behavior) (* what to do if the callee's execution fails *) ->
    responce_to_world


(* An element of type [contract_behavior] describes a behavior of an
   already called contract.  A contract has four ways of giving the
   control back to the world.
   1. returning
   2. failing
   3. commiting suicide
   4. calling some account
 *)
with contract_behavior :=
| ContractAction : contract_action -> responce_to_world -> contract_behavior
.


(* A useful function for reasoning.
   I was looking at http://adam.chlipala.net/cpdt/html/Coinductive.html
   around [frob].
 *)
Definition contract_action_expander (ca : contract_behavior) :=
  match ca with ContractAction a b => ContractAction a b end.

Lemma contract_action_expander_eq :
  forall ca, contract_action_expander ca = ca.
Proof.
  intro ca.
  case ca.
  auto.
Qed.




(**** Now we are able to specify contractsin terms of how they behave over
      many invocations, returns from calls and even re-entrance! ***)

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



(********* What the world does on an account ***********)

Inductive world_action :=
| WorldCall : call_env -> world_action
| WorldRet  : return_result -> world_action
| WorldFail : world_action
.

Definition world := list world_action.


(********
 When [world] and [respond_to_world] meet,
 they produce a sequence of events *)

Inductive action :=
| ActionByWorld : world_action -> action
| ActionByContract : contract_action -> action.

Definition history := list action.


(******** World and the contract interact to produce a history ****)

Fixpoint specification_run (w : world) (r : responce_to_world) : history :=
  match w, r with
  | nil, _ => nil
  | WorldCall call :: world_cont, Respond f _ _ =>
    match f call with
    | ContractAction cact contract_cont =>
      ActionByWorld (WorldCall call) ::
      ActionByContract cact ::
      specification_run world_cont contract_cont
    end
  | WorldRet ret :: world_cont, Respond _ r _ =>
    match (r ret) with
      ContractAction cact contract_cont =>
      ActionByWorld (WorldRet ret) ::
      ActionByContract cact ::
      specification_run world_cont contract_cont
    end
  | WorldFail :: world_cont, Respond _ _ (ContractAction cact contract_cont) =>
    ActionByWorld WorldFail ::
    ActionByContract cact ::
    specification_run world_cont contract_cont
  end.

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


(***
 *** Some more concrete view on EVM.
 *** This part is for interpreting bytecodes in terms of the abstract view above.
 ***)

(**
 ** Instructions
 **)

Inductive instruction :=
| PUSH1 : word -> instruction
| SLOAD
| SSTORE
| IJUMP
| CALLDATASIZE
| ADD
| SUB
| ISZERO
| CALL
| RETURN
.

(**
 ** Program
 **)

Definition program := list instruction.

Fixpoint drop_bytes (prog : list instruction) (bytes : nat) {struct bytes} :=
  match prog, bytes with
  | _, O => prog
  | PUSH1 v :: tl, S pre =>
    drop_bytes tl (pre - 2)
  | _ :: tl, S pre =>
    drop_bytes tl pre
  | nil, S _ => nil
  end.

(**
 ** Execution Environments
 **)

Axiom memory_state : Set. (* For now I don't use the memory *)
Axiom empty_memory : memory_state.
Axiom cut_memory : word -> word -> memory_state -> list byte.

Axiom cut_memory_zero_nil :
  forall start m, cut_memory start word_zero m = nil.


Definition storage := word -> word.

Record variable_env :=
  { venv_stack : list word
  ; venv_memory : memory_state
  ; venv_storage : storage
  ; venv_prg_sfx : list instruction
  ; venv_balance : address -> word
  ; venv_caller : address
  ; venv_value_sent : word
  }.

(* [update_balance adr v original] is similar to [original] except
   that [adr] is mapped to [v].
*)
Axiom update_balance : address -> word -> (address -> word) -> (address -> word).

Record constant_env :=
  { cenv_program : list instruction;
    cenv_this : address
  }.


(** Initialize variable_env variable_env . *)
Definition init_variable_env (s : storage) (bal : address -> word)
           (caller : address)
           (cenv : constant_env) (value : word) :=
  {|
    venv_stack := nil ;
    venv_memory := empty_memory ;
    venv_prg_sfx := cenv.(cenv_program) ;
    venv_storage := s ;
    venv_balance := bal ;
    venv_caller := caller ;
    venv_value_sent := value ;
  |}.


(**
 **  Meaning of an instruction.
 **)

Inductive instruction_result :=
| InstructionContinue : variable_env -> instruction_result
| InstructionToWorld : contract_action -> option variable_env (* to be pushed into the call stack *) -> instruction_result
.


Definition venv_update_stack (new_stack : list word) (v : variable_env) :=
  {|
    venv_stack := new_stack ;
    venv_memory := v.(venv_memory) ;
    venv_storage := v.(venv_storage) ;
    venv_prg_sfx := v.(venv_prg_sfx) ;
    venv_balance := v.(venv_balance) ;
    venv_caller := v.(venv_caller) ;
    venv_value_sent := v.(venv_value_sent)
  |}.

Definition venv_advance_pc (v : variable_env) :=
  {|
    venv_stack := v.(venv_stack) ;
    venv_memory := v.(venv_memory) ;
    venv_storage := v.(venv_storage) ;
    venv_prg_sfx := drop_one_element v.(venv_prg_sfx) ;
    venv_balance := v.(venv_balance) ;
    venv_caller := v.(venv_caller) ;
    venv_value_sent := v.(venv_value_sent)
  |}.


(** a general functoin for defining an instruction that
    pushes one element to the stack *)

Definition stack_0_1_op (v : variable_env) (c : constant_env) (w : word) : instruction_result :=
  InstructionContinue
    (venv_advance_pc (venv_update_stack (w :: v.(venv_stack)) v)).


(* These are just assumed for my laziness. *)
Axiom stack_1_1_op: variable_env -> constant_env ->
                    (word -> word) -> instruction_result.
Axiom stack_2_1_op: variable_env -> constant_env ->
                    (word -> word -> word) -> instruction_result.

Axiom sload : variable_env -> word -> word.
Axiom sstore : variable_env -> constant_env -> instruction_result.
Axiom ijump : variable_env -> constant_env -> instruction_result.
Axiom datasize : variable_env -> word.

Definition call (v : variable_env) (c : constant_env) : instruction_result :=
  match v.(venv_stack) with
  | e0 :: e1 :: e2 :: e3 :: e4 :: e5 :: e6 :: rest =>
    if word_smaller (v.(venv_balance) (c.(cenv_this))) e2 then
      InstructionToWorld ContractFail None
    else
    InstructionToWorld
      (ContractCall
         {|
           callarg_gaslimit := e0 ;
           callarg_code := address_of_word e1 ;
           callarg_recipient := address_of_word e1 ;
           callarg_value := e2 ;
           callarg_data := cut_memory e3 e4 v.(venv_memory) ;
           callarg_output_begin := e5 ;
           callarg_output_size := e6 ;
         |})
      (Some
         {|
           venv_stack := rest;
           venv_memory := v.(venv_memory);
           venv_storage := v.(venv_storage);
           venv_prg_sfx := drop_one_element (v.(venv_prg_sfx));
           venv_balance :=
             (update_balance (address_of_word e1)
                             (word_add (v.(venv_balance) (address_of_word e1)) e3)
             (update_balance c.(cenv_this)
                (word_sub (v.(venv_balance) (c.(cenv_this))) e3) v.(venv_balance)));
           venv_caller := v.(venv_caller);
           venv_value_sent := v.(venv_value_sent)
         |}
      )
  | _ =>
    InstructionToWorld ContractFail None (* this environment should disappear *)
  end.


Definition venv_returned_bytes v :=
  match v.(venv_stack) with
    | e0 :: e1 :: _ => cut_memory e0 e1 (v.(venv_memory))
    | _ => nil
  end.

Definition ret (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionToWorld (ContractReturn (venv_returned_bytes v)) None.

Require Import Coq.Program.Basics.

Definition instruction_sem (v : variable_env) (c : constant_env) (i : instruction)
  : instruction_result :=
  match i with
  | PUSH1 w => stack_0_1_op v c w
  | SLOAD => stack_1_1_op v c (sload v)
  | SSTORE => sstore v c
  | IJUMP => ijump v c
  | CALLDATASIZE => stack_0_1_op v c (datasize v)
  | ADD => stack_2_1_op v c word_add
  | SUB => stack_2_1_op v c word_sub
  | ISZERO => stack_1_1_op v c (compose bool_to_word word_iszero)
  | CALL => call v c
  | RETURN => ret v c
  end.

Inductive program_result :=
| ProgramStepRunOut : program_result
| ProgramToWorld : contract_action -> storage (* updated storage *) ->
                   (address -> word) (* updated balance *) ->
                   option variable_env (* to be pushed in the call stack *) -> program_result.


Fixpoint program_sem (v : variable_env) (c :constant_env) (steps : nat)
  : program_result :=
  match steps with
    | O => ProgramStepRunOut
    | S remaining_steps =>
      match v.(venv_prg_sfx) with
      | nil => ProgramToWorld ContractFail v.(venv_storage) v.(venv_balance) None
      | i :: _ =>
        match instruction_sem v c i with
        | InstructionContinue new_v =>
          program_sem new_v c remaining_steps
        | InstructionToWorld a opt_pushed_v =>
          ProgramToWorld a v.(venv_storage) v.(venv_balance) opt_pushed_v
        end
      end
  end.


(****** This program semantics has to be lifted to a history *****)

Record account_state :=
  { account_address : address
  ; account_storage : storage
  ; account_code : list instruction
  ; account_ongoing_calls : list variable_env
  }.

Definition account_state_update_storage new_st orig :=
  {| account_address := orig.(account_address);
     account_code    := orig.(account_code);
     account_storage := new_st;
     account_ongoing_calls := orig.(account_ongoing_calls)
  |}.

(** The ideas is that an account state defines a response_to_world **)

Definition build_envs_called (a : account_state) (env : call_env) :
  (variable_env * constant_env) :=
  ({|
      venv_stack := nil ;
      venv_memory := empty_memory;
      venv_prg_sfx := a.(account_code) ;
      venv_storage := a.(account_storage) ;
      venv_balance := env.(callenv_balance) ;
      venv_caller := env.(callenv_caller) ;
      venv_value_sent := env.(callenv_value)
   |}
   ,
    {|
      cenv_program := a.(account_code) ;
      cenv_this := a.(account_address)
   |}
  ).


Axiom build_envs_returned : account_state -> return_result -> option (variable_env * constant_env).
Axiom account_no_call_never_return :
  forall a r,
    a.(account_ongoing_calls) = nil -> build_envs_returned a r = None.

Axiom build_envs_fail : account_state -> option (variable_env * constant_env).
Axiom account_no_call_never_fail :
  forall a,
    a.(account_ongoing_calls) = nil -> build_envs_fail a = None.

(* Axiom update_account_state : account_state -> option variable_env -> account_state. *)

Definition update_account_state (prev : account_state) (v_opt : option variable_env) : account_state :=
  match v_opt with
  | None => prev
  | Some pushed =>
    {|
      account_address := prev.(account_address) ;
      account_storage := pushed.(venv_storage) ;
      account_code := prev.(account_code) ;
      account_ongoing_calls := pushed :: prev.(account_ongoing_calls)
    |}
  end.

(* [program_result_approximate a b] holds when
   a is identical to be or a still needs more steps *)
Definition program_result_approximate (a : program_result) (b : program_result)
:=
  a = ProgramStepRunOut \/ a = b.

Definition respond_to_call_correctly c a account_state_responds_to_world :=
      (forall (callenv : call_env)
          act continuation venv cenv,
          (venv, cenv) = build_envs_called a callenv ->
          c callenv = ContractAction act continuation ->
          exists pushed_venv, exists st, exists bal,
            (forall steps, program_result_approximate
             (program_sem venv cenv steps) (ProgramToWorld act st bal pushed_venv)) /\
              account_state_responds_to_world
                (account_state_update_storage st (update_account_state a pushed_venv))
                                          continuation).

Definition respond_to_return_correctly (r : return_result -> contract_behavior)
           (a : account_state)
           (account_state_responds_to_world : account_state -> responce_to_world -> Prop) :=
  forall (rr : return_result) venv cenv continuation act,
     Some (venv, cenv) = build_envs_returned a rr ->
     r rr = ContractAction act continuation ->
     exists pushed_venv, exists st, exists bal,
     (forall steps,
         program_result_approximate (program_sem venv cenv steps)
                                    (ProgramToWorld act st bal pushed_venv))
     /\
    account_state_responds_to_world (update_account_state a pushed_venv)
                                    continuation.

Definition respond_to_fail_correctly (f : contract_behavior)
           (a : account_state)
           (account_state_responds_to_world : account_state -> responce_to_world -> Prop) :=
  forall (rr : return_result) venv cenv continuation act,
     Some (venv, cenv) = build_envs_fail a ->
     f = ContractAction act continuation ->
     exists pushed_venv, exists st, exists bal,
     (forall steps,
         program_result_approximate (program_sem venv cenv steps)
                                    (ProgramToWorld act st bal pushed_venv))
     /\
    account_state_responds_to_world (update_account_state a pushed_venv)
                                    continuation.



CoInductive account_state_responds_to_world :
  account_state -> responce_to_world -> Prop :=
| AccountStep :
    forall (a : account_state)
           (c : call_env -> contract_behavior)
           (r : return_result -> contract_behavior) f,
      respond_to_call_correctly c a account_state_responds_to_world ->
      respond_to_return_correctly r a account_state_responds_to_world ->
      respond_to_fail_correctly f a account_state_responds_to_world ->
    account_state_responds_to_world a (Respond c r f)
.


Section Example1_Continue.
(*** prove that example 1 has an implementation  *)

  Definition return_result_nil : return_result := nil.
  Definition action_example_1 :=
    always_return return_result_nil.

  Definition spec_example_1 : responce_to_world :=
    Respond
      (fun _ => action_example_1)
      (fun _ => action_example_1)
      action_example_1.

  Variable example1_address : address.
  Definition empty_storage : storage :=
    fun _ => word_zero.

  Definition example1_program : list instruction :=
    PUSH1 word_zero ::
    PUSH1 word_zero ::
    RETURN ::
    nil.

  Definition example1_account_state :=
    {| account_address := example1_address ;
       account_storage := empty_storage ;
       account_code := example1_program ;
       account_ongoing_calls := nil |}.

  Require Coq.Setoids.Setoid.
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

  Theorem example1_spec_impl_match :
    account_state_responds_to_world
      example1_account_state spec_example_1.
  Proof.
    cofix.
    apply AccountStep.
    { (* call case *)
      unfold respond_to_call_correctly.
      intros.
      exists None.
      exists venv.(venv_storage).
      exists venv.(venv_balance).
      split.
      {
        intro.
        case steps.
        {
          unfold program_result_approximate.
          auto.
        }
        intro n; case n.
        {
          unfold program_result_approximate.
          inversion H; subst.
          auto.
        }
        intro m; case m.
        {
          unfold program_result_approximate.
          (* sorry I use automatically generated names. *)
          inversion H; subst.
          auto.
        }
        intro.
        inversion H; subst.
        simpl.
        unfold venv_update_stack.
        simpl.
        unfold action_example_1 in H0.
        rewrite always_return_def in H0.
        inversion H0; subst.
        unfold venv_advance_pc; simpl.
        unfold venv_returned_bytes; simpl.
        unfold program_result_approximate.
        right.
        f_equal.
        f_equal.
        rewrite cut_memory_zero_nil.
        auto.
      }
      {
        unfold update_account_state.
        unfold action_example_1 in H0.
        rewrite always_return_def in H0.
        inversion H0; subst.
        unfold build_envs_called in H.
        inversion H; subst; simpl.
        apply example1_spec_impl_match.
      }
    }
    {
      unfold respond_to_return_correctly.
      intros.
      rewrite account_no_call_never_return in H; auto.
      congruence.
    }
    {
      unfold respond_to_fail_correctly.
      intros.
      rewrite account_no_call_never_fail in H; auto.
      congruence.
    }
  Qed.

End Example1_Continue.
