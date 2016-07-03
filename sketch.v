(* EVM Contract Behavior Formalization *)
(* for Coq 8.5pl1 *)

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

Module Type Word.
  Parameter word  : Set.      (* Does anyone know a good uint256 library for Coq? *)
  Parameter word_eq : word -> word -> bool.
  Parameter word_add : word -> word -> word.
  Parameter word_sub : word -> word -> word.
  Parameter word_one : word.
  Parameter word_zero : word.
  Parameter word_iszero : word -> bool.
  (* TODO: state correctness of word_iszero *)
  Parameter word_smaller : word -> word -> bool.
  Parameter word_of_N : N -> word.
  Parameter N_of_word : word -> N.

  Open Scope N_scope.
  Parameter N_of_word_of_N :
    (* TODO: This 10000 is a bit arbitrary. *)
  forall (n : N), n < 10000 -> N_of_word (word_of_N n) = n.

  Parameter byte : Set.
  Parameter address : Set.
  Parameter address_of_word : word -> address.

  Parameter word_nth_byte : word -> nat -> byte.

  (* list of bytes [a; b; c] as (a * 256 + b) * 256 + c *)
  Parameter word_of_bytes : list byte -> word.

  Require Import Coq.Lists.List.
  Import ListNotations.
  Open Scope list_scope.

  Parameter words_of_nth_bytes :
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

  Parameter event : Set. (* logged events *)


  (* These depends on the choice of word.
   * In the concrete case, these can be MSet or FSet.
   *)
  Parameter memory_state : Set. (* For now I don't use the memory *)
  Parameter empty_memory : memory_state.
  Parameter cut_memory : word -> word -> memory_state -> list byte.
  Parameter cut_memory_zero_nil :
    forall start m, cut_memory start word_zero m = nil.

End Word.

Module ContractSem (W : Word).
Export W.

Definition bool_to_word (b : bool) :=
  if b then word_one else word_zero.

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
| JUMP
| JUMPI
| JUMPDEST
| CALLDATASIZE
| ADD
| SUB
| ISZERO
| CALL
| RETURN
| STOP
| DUP1
| POP
.

(**
 ** Program
 **)

Definition program := list instruction.

Print N.

Require Import Recdef.

Function drop_bytes (prog : list instruction) (bytes : N)
         :=
  match prog, bytes with
  | _, N0 => prog
  | PUSH1 v :: tl, _ =>
    drop_bytes tl (bytes - 2)
  | _ :: tl, _ =>
    drop_bytes tl (bytes - 1)
  | nil, _ => nil
  end.


(**
 ** Execution Environments
 **)

Definition storage := word -> word. (* TODO maybe this should be FSet *)

Definition empty_storage : storage :=
  fun _ => word_zero.

Record variable_env :=
  { venv_stack : list word
  ; venv_memory : memory_state
  ; venv_storage : storage
  ; venv_prg_sfx : list instruction
  ; venv_balance : address -> word
  ; venv_caller : address
  ; venv_value_sent : word
  (* TODO: add the sequence of executed instructions.
     would be useful for calculating the gas *)
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

Definition instruction_failure_result :=
  InstructionToWorld ContractFail None.

Definition instruction_return_result (x: return_result) :=
  InstructionToWorld (ContractReturn x) None.


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

Arguments venv_advance_pc v /.

Require Import List.

Fixpoint venv_pop_stack (n : nat) (v : variable_env) :=
  match n with
  | O => v
  | S m =>
    venv_update_stack
      (tl v.(venv_stack))
      (venv_pop_stack m v)
  end.

Definition venv_stack_top (v : variable_env) : option word :=
  match v.(venv_stack) with
  | h :: _ => Some h
  | _ => None
  end.

Definition venv_change_sfx (pos : N) (v : variable_env)
  (c : constant_env) : variable_env :=
  {|
    venv_stack := v.(venv_stack) ;
    venv_memory := v.(venv_memory);
    venv_storage := v.(venv_storage);
    venv_prg_sfx := drop_bytes c.(cenv_program) pos ;
    venv_balance := v.(venv_balance);
    venv_caller := v.(venv_caller);
    venv_value_sent := v.(venv_value_sent);
  |}.

Definition venv_first_instruction (v : variable_env) : option instruction :=
  hd_error v.(venv_prg_sfx).

(** a general functoin for defining an instruction that
    pushes one element to the stack *)

Definition stack_0_0_op (v : variable_env) (c : constant_env)
  : instruction_result :=
  InstructionContinue (venv_advance_pc v).

Definition stack_0_1_op (v : variable_env) (c : constant_env) (w : word) : instruction_result :=
  InstructionContinue
    (venv_advance_pc (venv_update_stack (w :: v.(venv_stack)) v)).


(* These are just assumed for my laziness. *)
Definition stack_1_1_op (v: variable_env) (c : constant_env)
                    (f : word -> word) : instruction_result :=
  match v.(venv_stack) with
    | nil => instruction_failure_result
    | h :: t =>
      InstructionContinue
        (venv_advance_pc (venv_update_stack (f h :: t) v))
  end.

Definition stack_1_2_op (v: variable_env) (c : constant_env)
           (f : word -> (word (* new head *) * word (* new second*) ))
  : instruction_result :=
  match v.(venv_stack) with
    | nil => instruction_failure_result
    | h :: t =>
      match f h with
        (new0, new1) =>
        InstructionContinue
          (venv_advance_pc (venv_update_stack (new0 :: new1 :: t) v))
      end
  end.

Axiom stack_2_1_op: variable_env -> constant_env ->
                    (word -> word -> word) -> instruction_result.

Definition sload (v : variable_env) (idx : word) : word :=
  v.(venv_storage) idx.

Axiom sstore : variable_env -> constant_env -> instruction_result.

Definition jump (v : variable_env) (c : constant_env) : instruction_result :=
  match venv_stack_top v with
  | None => instruction_failure_result
  | Some pos =>
    let v_new := venv_change_sfx (N_of_word pos) (venv_pop_stack 1 v) c in
    match venv_first_instruction v_new with
    | Some JUMPDEST =>
        InstructionContinue v_new
    | _ => instruction_failure_result
    end
  end.

Definition jumpi (v : variable_env) (c : constant_env) : instruction_result :=
  match v.(venv_stack) with
  | pos :: cond :: rest =>
    if word_iszero cond then
      InstructionContinue (venv_advance_pc (venv_pop_stack 2 v))
    else
      jump (venv_pop_stack 1 v) c (* this has to change when gas is considered *)
  | _ => instruction_failure_result
  end.


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

Arguments venv_returned_bytes v /.

Definition ret (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionToWorld (ContractReturn (venv_returned_bytes v)) None.

Axiom stop : variable_env -> constant_env -> instruction_result.
Axiom pop : variable_env -> constant_env -> instruction_result.

Require Import Coq.Program.Basics.

Definition instruction_sem (v : variable_env) (c : constant_env) (i : instruction)
  : instruction_result :=
  match i with
  | PUSH1 w => stack_0_1_op v c w
  | SLOAD => stack_1_1_op v c (sload v)
  | SSTORE => sstore v c
  | JUMPI => jumpi v c
  | JUMP => jump v c
  | JUMPDEST => stack_0_0_op v c
  | CALLDATASIZE => stack_0_1_op v c (datasize v)
  | ADD => stack_2_1_op v c word_add
  | SUB => stack_2_1_op v c word_sub
  | ISZERO => stack_1_1_op v c (compose bool_to_word word_iszero)
  | CALL => call v c
  | RETURN => ret v c
  | STOP => stop v c
  | DUP1 => stack_1_2_op v c (fun a => (a, a))
  | POP => pop v c
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

Definition build_venv_called (a : account_state) (env : call_env) :
  variable_env :=
  {|
      venv_stack := nil ;
      venv_memory := empty_memory;
      venv_prg_sfx := a.(account_code) ;
      venv_storage := a.(account_storage) ;
      venv_balance := env.(callenv_balance) ;
      venv_caller := env.(callenv_caller) ;
      venv_value_sent := env.(callenv_value)
   |}.

Arguments build_venv_called a env /.

Definition build_cenv (a : account_state) :
    constant_env :=
    {|
      cenv_program := a.(account_code) ;
      cenv_this := a.(account_address)
   |}.


(* must push 1 to the stack.  balance should be updated. *)
Axiom build_venv_returned : account_state -> return_result -> option variable_env.
Axiom account_no_call_never_return :
  forall a r,
    a.(account_ongoing_calls) = nil -> build_venv_returned a r = None.

(* must push 0 to the stack.  balance should be updated too *)
Axiom build_venv_fail : account_state -> option variable_env.
Axiom account_no_call_never_fail :
  forall a,
    a.(account_ongoing_calls) = nil -> build_venv_fail a = None.

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
   a is identical to b or a still needs more steps *)
Definition program_result_approximate (a : program_result) (b : program_result)
:=
  a = ProgramStepRunOut \/ a = b
  (* TODO: this [a = b] has to be weakened up to 2^256 in many places *).

Definition respond_to_call_correctly c a account_state_responds_to_world :=
      (forall (callenv : call_env)
          act continuation,
          c callenv = ContractAction act continuation ->
          exists pushed_venv, exists st, exists bal,
            (forall steps, program_result_approximate
             (program_sem (build_venv_called a callenv)
                          (build_cenv a) steps)
             (ProgramToWorld act st bal pushed_venv)) /\
              account_state_responds_to_world
                (account_state_update_storage st (update_account_state a pushed_venv))
                                          continuation).

Definition respond_to_return_correctly (r : return_result -> contract_behavior)
           (a : account_state)
           (account_state_responds_to_world : account_state -> responce_to_world -> Prop) :=
  forall (rr : return_result) venv cenv continuation act,
     Some venv = build_venv_returned a rr ->
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
     Some venv = build_venv_fail a ->
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

End ContractSem.


Module AbstractExamples (W : Word).
  Module C := (ContractSem W).
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

  Definition spec_example_0 : responce_to_world :=
    Respond
      (fun _ => always_fail)
      (fun _ => always_fail)
      always_fail.

  Variable example0_address : address.

  Definition example0_program :=
    PUSH1 (word_of_N 0) ::
    JUMP :: nil.

  Definition example0_account_state :=
    {| account_address := example0_address ;
       account_storage := empty_storage ;
       account_code := example0_program ;
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

  Theorem example0_spec_impl_match :
    account_state_responds_to_world
      example0_account_state spec_example_0.
  Proof.
    cofix.
    apply AccountStep.
    {
      intros ? ? ? ?.
      always_fail_tac.
      eexists.
      eexists.
      eexists.
      split.
      {
        intros steps.
        case steps as [ | steps]; [ try left; auto | ].
        case steps as [ | steps]; [ try left; auto | ].
        simpl.
        unfold jump; simpl.
        unfold build_venv_called; simpl.
        unfold venv_update_stack; simpl.
        unfold venv_change_sfx; simpl.
        unfold venv_first_instruction; simpl.
        rewrite N_of_word_of_N.
        { simpl.
          right.
          auto. }
        reflexivity.
      }
      {
        assumption.
      }
    }
    {
      unfold respond_to_return_correctly.
      intros rr venv cenv continuation act.
      rewrite account_no_call_never_return; auto.
      congruence.
    }
    {
      unfold respond_to_fail_correctly.
      intros venv cenv continuation act.
      rewrite account_no_call_never_fail; auto.
      congruence.
    }
  Qed.

End Example0Continue.


Section Example1Continue.
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
    account_state_responds_to_world
      example1_account_state spec_example_1.
  Proof.
    cofix.
    apply AccountStep.
    { (* call case *)
      unfold respond_to_call_correctly.
      intros.
      eexists.
      eexists.
      eexists.
      split.
      {
        intro.
        case steps as [|steps]; [left; auto | ].
        case steps as [|steps]; [left; auto | ].
        case steps as [|steps]; [left; auto | ].
        unfold action_example_1 in H.
        always_return_tac.
        right.
        simpl.
        f_equal.
        f_equal.
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
      intros ? ? ? ? ?.
      rewrite account_no_call_never_return; auto.
      congruence.
    }
    {
      intros ? ? ? ?.
      rewrite account_no_call_never_fail; auto.
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

  Print W.ops.

  Definition word_eq (a : W.t) (b : W.t) :=
    match ZnZ.compare a b with Eq => true | _ => false end.

  Definition word_add (a b : W.t) :=
    ZnZ.add a b.

  Definition word_sub := ZnZ.sub.

  Definition word_one := ZnZ.one.

  Definition word_zero := ZnZ.zero.

  Definition word_iszero := ZnZ.eq0.

  Definition word_smaller a b :=
    match ZnZ.compare a b with Lt => true | _ => false end.

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
      admit.
    }
    {
      admit.
    }
  Admitted.


  Definition raw_byte := B.t.
  Inductive byte' :=
  | ByteRaw : raw_byte -> byte'
  | ByteOfWord : word -> nat -> byte'
  .
  Definition byte := byte'.

  Definition address := A.t.

  Definition address_of_word (w : word) : address := w.

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

End ConcreteWord.


Module ExamplesOnConcreteWord.

  Module ConcreteSem := (ContractSem ConcreteWord).
  Include ConcreteSem.

  Definition example2_program : program :=
    PUSH1 (word_of_N 0) ::
    SLOAD ::
    DUP1 ::
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
    POP ::
    PUSH1 (word_of_N 1) ::
    SUB ::
    PUSH1 (word_of_N 0) ::
    SSTORE ::
    STOP ::
    nil.

  Variable example2_address : address.

  Definition example2_account_state :=
    {| account_address := example2_address ;
       account_storage := empty_storage ;
       account_code := example2_program ;
       account_ongoing_calls := nil |}.


Variable something_to_call : call_arguments.

(* TODO: remove duplicate somehow *)
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

  Lemma call_but_fail_on_reentrace_0_eq :
    call_but_fail_on_reentrance 0 =
    Respond
      (fun _ =>
         ContractAction (ContractCall something_to_call)
              (call_but_fail_on_reentrance (S O)))
      (fun _ => ContractAction ContractFail (call_but_fail_on_reentrance O))
      (ContractAction ContractFail (call_but_fail_on_reentrance O)).
  Admitted.

  Definition example2_spec : responce_to_world :=
    call_but_fail_on_reentrance 0.

  Theorem example2_spec_impl_match :
    account_state_responds_to_world
      example2_account_state example2_spec.
  Proof.
    cofix.
    unfold example2_spec.
    rewrite call_but_fail_on_reentrace_0_eq.
    apply AccountStep.
    {
      unfold respond_to_call_correctly.
      intros ce a con next.
      eexists.
      eexists.
      eexists.
      split.
      {
        intro s.
        case s as [| s]; [ simpl; left; auto | ].
        case s as [| s]; [ simpl; left; auto | ].
        case s as [| s]; [ simpl; left; auto | ].
        case s as [| s]; [ simpl; left; auto | ].
        case s as [| s]; [ simpl; left; auto | ].
        case s as [| s]; [ simpl; left; auto | ].
        case s as [| s]; [ simpl; left; auto | ].
        (* this automatically detects that the first JUMPI is not fired *)
        case s as [| s]; [ simpl; left; auto | ].
        case s as [| s]; [ simpl; left; auto | ].

        (* here the definition of add is needed *)
        admit. admit.
      }
      {
        admit.
      }
    }
    {
      admit.
    }
    {
      admit.
    }
  Admitted.

End ExamplesOnConcreteWord.
