Require Import NArith.
Require Import Word.

Module Make (W : Word).
Export W.

Definition bool_to_word (b : bool) :=
  if b then word_one else word_zero.

Arguments bool_to_word b /.

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


(* An element of type [response_to_world] describes a strategy of a contract
   that can respond when
   1. it is called from the world
   2. it receives a callee return from the world
   3. it receives a callee failure from the world.
   Initially, when the contract has not called any other accounts,
   the points 2. and 3. are useless.
 *)
CoInductive response_to_world :=
| Respond :
    (call_env -> contract_behavior) (* what to do if called / or re-entered *) ->
    (return_result -> contract_behavior) (* what to do if the callee returns (if exists) *) ->
    (contract_behavior) (* what to do if the callee's execution fails *) ->
    response_to_world


(* An element of type [contract_behavior] describes a behavior of an
   already called contract.  A contract has four ways of giving the
   control back to the world.
   1. returning
   2. failing
   3. commiting suicide
   4. calling some account
 *)
with contract_behavior :=
| ContractAction : contract_action -> response_to_world -> contract_behavior
.


(* A useful function for reasoning.
   I was looking at http://adam.chlipala.net/cpdt/html/Coinductive.html
   around [frob].
 *)
Definition contract_action_expander (ca : contract_behavior) :=
  match ca with ContractAction a b => ContractAction a b end.

Definition response_expander (r : response_to_world) :=
  match r with Respond f g h => Respond f g h end.

Lemma contract_action_expander_eq :
  forall ca, contract_action_expander ca = ca.
Proof.
  intro ca.
  case ca.
  auto.
Qed.

Lemma response_expander_eq :
  forall r, r = response_expander r.
Proof.
  intro r.
  case r.
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

Fixpoint specification_run (w : world) (r : response_to_world) : history :=
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
| CALLDATALOAD
| CALLVALUE
| ADD
| SUB
| ISZERO
| CALL
| RETURN
| STOP
| DUP1
| POP
| GASLIMIT
| instr_GT
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

Record variable_env :=
  { venv_stack : list word
  ; venv_memory : memory_state
  ; venv_storage : storage
  ; venv_prg_sfx : list instruction
  ; venv_balance : address -> word (* does this blong here?*)
  ; venv_caller : address
  ; venv_value_sent : word
  ; venv_data_sent : list byte
  (* TODO: add the sequence of executed instructions.
     would be useful for calculating the gas *)

  (* These are necessary when throwing. *)
  ; venv_storage_at_call : storage
  ; venv_balance_at_call : address -> word

  (* TODO: use venv_balance_at_call somewhere *)
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
           (cenv : constant_env) (value : word) (data : list byte) :=
  {|
    venv_stack := nil ;
    venv_memory := empty_memory ;
    venv_prg_sfx := cenv.(cenv_program) ;
    venv_storage := s ;
    venv_balance := bal ;
    venv_caller := caller ;
    venv_value_sent := value ;
    venv_data_sent := data ;
    venv_storage_at_call := s ;
    venv_balance_at_call := bal ;
  |}.


(**
 **  Meaning of an instruction.
 **)

Inductive instruction_result :=
| InstructionContinue : variable_env -> instruction_result
| InstructionToWorld : contract_action -> option variable_env (* to be pushed into the call stack *) -> instruction_result
| InstructionInvalid : instruction_result (* PUSH1 with more than 255 *)
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
    venv_value_sent := v.(venv_value_sent) ;
    venv_data_sent := v.(venv_data_sent) ;
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
  |}.

Arguments venv_update_stack new_stack v /.

Definition venv_advance_pc (v : variable_env) :=
  {|
    venv_stack := v.(venv_stack) ;
    venv_memory := v.(venv_memory) ;
    venv_storage := v.(venv_storage) ;
    venv_prg_sfx := drop_one_element v.(venv_prg_sfx) ;
    venv_balance := v.(venv_balance) ;
    venv_caller := v.(venv_caller) ;
    venv_value_sent := v.(venv_value_sent) ;
    venv_data_sent := v.(venv_data_sent) ;
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
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
    venv_data_sent := v.(venv_data_sent);
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
  |}.

Arguments venv_change_sfx pos v c /.

Definition function_update (addr : word) (val : word) (f : word -> word) : (word -> word) :=
  fun x => (if word_eq x addr then val else f x).

Definition venv_update_storage (addr : word) (val : word) (v : variable_env)
           : variable_env :=
  {|
    venv_stack := v.(venv_stack) ;
    venv_memory := v.(venv_memory);
    venv_storage := storage_store addr val v.(venv_storage);
    venv_prg_sfx := v.(venv_prg_sfx);
    venv_balance := v.(venv_balance);
    venv_caller := v.(venv_caller);
    venv_value_sent := v.(venv_value_sent);
    venv_data_sent := v.(venv_data_sent);
    venv_storage_at_call := v.(venv_storage_at_call) ;
    venv_balance_at_call := v.(venv_balance_at_call)
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

Definition stack_2_1_op (v : variable_env) (c : constant_env)
                    (f : word -> word -> word) : instruction_result :=
  match v.(venv_stack) with
    | operand0 :: operand1 :: rest =>
      InstructionContinue (venv_advance_pc
                             (venv_update_stack (f operand0 operand1 :: rest) v))
    | _ => instruction_failure_result
  end.

Definition sload (v : variable_env) (idx : word) : word :=
  storage_load v.(venv_storage) idx.

Arguments sload v idx /.

Definition sstore (v : variable_env) (c : constant_env) : instruction_result :=
  match v.(venv_stack) with
    | addr :: val :: stack_tail =>
      InstructionContinue
        (venv_advance_pc
           (venv_update_stack stack_tail
                              (venv_update_storage addr val v)))
    | _ => instruction_failure_result
  end.

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

Arguments jump v c /.

Definition jumpi (v : variable_env) (c : constant_env) : instruction_result :=
  match v.(venv_stack) with
  | pos :: cond :: rest =>
    if word_iszero cond then
      InstructionContinue (venv_advance_pc (venv_pop_stack 2 v))
    else
      jump (venv_pop_stack 1 v) c (* this has to change when gas is considered *)
  | _ => instruction_failure_result
  end.

Arguments jumpi v c /.


Search _ (nat -> Z).

Definition datasize (v : variable_env) : word :=
  word_of_nat (List.length v.(venv_data_sent)).

Axiom cut_data : variable_env -> word -> word.

(* currently this is not very true: to fix, add the sequence of executed instructions in venv. *)
Axiom gas_limit : variable_env -> word.

(* TODO: this should fail for various reasons.  lack of balance. *)
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
      (Some (* TODO: this part should be abstracted away *)
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
           venv_value_sent := v.(venv_value_sent) ;
           venv_data_sent := v.(venv_data_sent) ;
           venv_storage_at_call := v.(venv_storage_at_call) ;
           venv_balance_at_call := v.(venv_balance_at_call)
         |}
      )
  | _ =>
    InstructionToWorld ContractFail None (* this environment should disappear *)
  end.

Arguments call v c /.


Definition venv_returned_bytes v :=
  match v.(venv_stack) with
    | e0 :: e1 :: _ => cut_memory e0 e1 (v.(venv_memory))
    | _ => nil
  end.

Arguments venv_returned_bytes v /.

Definition ret (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionToWorld (ContractReturn (venv_returned_bytes v)) None.

Definition stop (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionToWorld (ContractReturn nil) None.

Definition pop (v : variable_env) (c : constant_env) : instruction_result :=
  InstructionContinue
    (venv_advance_pc (venv_update_stack
       (tail v.(venv_stack))
       v)).

Require Import Coq.Program.Basics.

Definition instruction_sem (v : variable_env) (c : constant_env) (i : instruction)
  : instruction_result :=
  match i with
  | PUSH1 w =>
    if word_smaller w (word_of_N 256%N) then
      stack_0_1_op v c w
    else
      InstructionInvalid
  | SLOAD => stack_1_1_op v c (sload v)
  | SSTORE => sstore v c
  | JUMPI => jumpi v c
  | JUMP => jump v c
  | JUMPDEST => stack_0_0_op v c
  | CALLDATASIZE => stack_0_1_op v c (datasize v)
  | CALLDATALOAD => stack_1_1_op v c (cut_data v)
  | CALLVALUE => stack_0_1_op v c v.(venv_value_sent)
  | ADD => stack_2_1_op v c word_add
  | SUB => stack_2_1_op v c word_sub
  | ISZERO => stack_1_1_op v c (compose bool_to_word word_iszero)
  | CALL => call v c
  | RETURN => ret v c
  | STOP => stop v c
  | DUP1 => stack_1_2_op v c (fun a => (a, a))
  | POP => pop v c
  | GASLIMIT => stack_0_1_op v c (gas_limit v)
  | instr_GT => stack_2_1_op v c (fun a b => bool_to_word (word_smaller b a))
  end.

Inductive program_result :=
| ProgramStepRunOut : program_result
| ProgramToWorld : contract_action ->
                   storage (* updated storage *) ->
                   (address -> word) (* updated balance *) ->
                   option variable_env (* to be pushed in the call stack *) -> program_result
| ProgramInvalid : program_result
.


Fixpoint program_sem (v : variable_env) (c :constant_env) (steps : nat)
  : program_result :=
  match steps with
    | O => ProgramStepRunOut
    | S remaining_steps =>
      match v.(venv_prg_sfx) with
      | nil => ProgramToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) None
      | i :: _ =>
        match instruction_sem v c i with
        | InstructionContinue new_v =>
          program_sem new_v c remaining_steps
        | InstructionToWorld ContractFail opt_pushed_v =>
          ProgramToWorld ContractFail v.(venv_storage_at_call) v.(venv_balance_at_call) opt_pushed_v
        | InstructionToWorld a opt_pushed_v =>
          ProgramToWorld a v.(venv_storage) v.(venv_balance) opt_pushed_v
        (* TODO: change the balance when suicide *)
        | InstructionInvalid => ProgramInvalid
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

Arguments account_state_update_storage new_st orig /.

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
      venv_value_sent := env.(callenv_value) ;
      venv_data_sent := env.(callenv_data) ;
      venv_storage_at_call := a.(account_storage) ;
      venv_balance_at_call := env.(callenv_balance)
   |}.

Arguments build_venv_called a env /.

Definition build_cenv (a : account_state) :
    constant_env :=
    {|
      cenv_program := a.(account_code) ;
      cenv_this := a.(account_address)
   |}.


(* TODO: update the storage according to a *)
(* TODO: udpate the balance according to return_result *)
Definition build_venv_returned
  (a : account_state) (r : return_result) : option variable_env :=
  match a.(account_ongoing_calls) with
  | nil => None
  | recovered :: _ =>
    Some (venv_update_stack (word_one :: recovered.(venv_stack)) recovered)
         (* TODO: actually, need to update the memory *)
  end.

Arguments build_venv_returned a r /.

(* Since the callee failed, the balance should not be updated. *)
Definition build_venv_fail
           (a : account_state) : option variable_env :=
  match a.(account_ongoing_calls) with
  | nil => None
  | recovered :: _ =>
    Some (venv_update_stack (word_zero :: recovered.(venv_stack)) recovered)
  end.

Arguments build_venv_fail a /.

Definition account_state_pop_ongoing_call (orig : account_state) :=
  {| account_address := orig.(account_address);
     account_storage := orig.(account_storage);
     account_code := orig.(account_code);
     account_ongoing_calls := tail (orig.(account_ongoing_calls))
  |}.

Arguments account_state_pop_ongoing_call orig /.

(* TODO: use venv widely and remove other arguments *)
Definition update_account_state (prev : account_state) (act: contract_action)
           (st : storage) (bal : address -> word)
           (v_opt : option variable_env) : account_state :=
  account_state_update_storage st
        match v_opt with
        | None =>
          prev
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

Definition respond_to_call_correctly c a I account_state_responds_to_world :=
      (forall (callenv : call_env)
          act continuation,
          I (build_venv_called a callenv) (build_cenv a) /\
          (I (build_venv_called a callenv) (build_cenv a) ->
           c callenv = ContractAction act continuation ->
          exists pushed_venv, exists st, exists bal,
            (forall steps, program_result_approximate
             (program_sem (build_venv_called a callenv)
                          (build_cenv a) steps)
             (ProgramToWorld act st bal pushed_venv)) /\
              account_state_responds_to_world
                (account_state_update_storage st (update_account_state a act st bal pushed_venv))
                                          continuation I)).

Definition respond_to_return_correctly (r : return_result -> contract_behavior)
           (a : account_state) I
           account_state_responds_to_world :=
  forall (rr : return_result) venv continuation act,
     Some venv = build_venv_returned a rr ->
     I venv (build_cenv a) /\
     (I venv (build_cenv a) ->
     r rr = ContractAction act continuation ->
     exists pushed_venv, exists st, exists bal,
     (forall steps,
         program_result_approximate (program_sem venv (build_cenv a) steps)
                                    (ProgramToWorld act st bal pushed_venv))
     /\
    account_state_responds_to_world
      (update_account_state (account_state_pop_ongoing_call a) act st bal pushed_venv)
                                    continuation I).

Definition respond_to_fail_correctly (f : contract_behavior)
           (a : account_state) (I : variable_env -> constant_env -> Prop)
           account_state_responds_to_world :=
  forall venv continuation act,
     Some venv = build_venv_fail a ->
     I venv (build_cenv a) /\
     (I venv (build_cenv a) ->
     f = ContractAction act continuation ->
     exists pushed_venv, exists st, exists bal,
     (forall steps,
         program_result_approximate (program_sem venv (build_cenv a) steps)
                                    (ProgramToWorld act st bal pushed_venv))
     /\
    account_state_responds_to_world
      (update_account_state (account_state_pop_ongoing_call a) act st bal pushed_venv)
                                    continuation I).



CoInductive account_state_responds_to_world :
  account_state -> response_to_world -> (variable_env -> constant_env -> Prop (*invariant*)) -> Prop :=
| AccountStep :
    forall (a : account_state)
           (c : call_env -> contract_behavior)
           (r : return_result -> contract_behavior)
           (I : variable_env -> constant_env -> Prop)
           f,
      respond_to_call_correctly c a I account_state_responds_to_world ->
      respond_to_return_correctly r a I account_state_responds_to_world ->
      respond_to_fail_correctly f a I account_state_responds_to_world ->
    account_state_responds_to_world a (Respond c r f) I
.

End Make.
