theory Sketch

imports Main "~~/src/HOL/Word/Word"

begin

type_synonym uint256 = "256 word"
type_synonym byte    = "8 word"
type_synonym address = "160 word"

record call_arguments =
    callarg_gaslimit    :: uint256
    callarg_code        :: address
    callarg_recipient   :: address
    callarg_value       :: uint256
    callarg_data        :: "byte list"
    callarg_output_begin :: uint256
    callarg_output_size :: uint256
  
record call_env =
  callenv_gaslimit :: uint256
  callenv_value :: uint256
  callenv_data :: "byte list"
  callenv_caller :: address
  callenv_timestap :: uint256
  callenv_blocknum :: uint256
  callenv_balance :: "address => uint256" 
    
record return_result =
  return_result_bytes :: "byte list"
  
datatype contract_action =
  ContractCall call_arguments
  (* [Call args continuation] is the behavior of [CALL] instruction
      together with all behaviors shown by the account after the [CALL].
     [args] represents the parameters of a call.
     [continuation] represents the behavior shown after the [CALL]
     instruction.  See the comment at [after_call_behavior].
   *)
| ContractFail
  (* [Fail] is the behavior of runtime errors (e.g. jumping to an invalid
     program counter / lack of gas *)
| ContractSuicide
| ContractReturn return_result (* returned data *)
  (* [Return ret next] is the behavior of a [RETURN], [STOP] instruction.
     Upon the next call with [env], [next env] will be the contract behavior.
   *)

codatatype responce_to_world =
  Respond
    "call_env => contract_behavior" (* what to do if called / or re-entered *)
 (*   "return_result => contract_behavior" (* what to do if the callee returns (if exists) *)
    "contract_behavior" (* what to do if the callee's execution fails *) *)

and contract_behavior =
  ContractAction contract_action responce_to_world
  
(* Example 0: a contract that always fails *)
primcorec always_fail :: contract_behavior
      and always_fail_response :: responce_to_world
where
  "always_fail = 
            ContractAction ContractFail always_fail_response"
| "always_fail_response =
                 Respond (\<lambda> _. always_fail)
                      (*   (\<lambda> _. always_fail)
                         always_fail *)"
                         
                         
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


datatype instruction =
  PUSH1 byte
| SLOAD
| SSTORE
| JUMP
| IJUMP
| JUMPDEST
| CALLDATASIZE
| ADD
| SUB
| ISZERO
| CALL
| RETURN

type_synonym program = "instruction list"

fun drop_bytes :: "program \<Rightarrow> nat \<Rightarrow> program"
where
  "drop_bytes prog 0 = prog"
| "drop_bytes (PUSH1 v # tail) (Suc pre) =
   drop_bytes tail (pre - 1)"
| "drop_bytes (_ # tail) (Suc pre) =
   drop_bytes tail pre"
| "drop_bytes [] (Suc _) = []"

type_synonym memory_state = "uint256 \<Rightarrow> byte"
definition empty_memory :: memory_state where
"empty_memory x = 0"

function cut_memory :: "uint256 => uint256 => memory_state => byte list"
where
  "cut_memory _ 0 _ = []"
| "x \<noteq> 0 \<Longrightarrow> cut_memory _ x _ = undefined" (* I just need to define this properly *)
apply(auto)
apply(blast)
done

type_synonym storage = "uint256 \<Rightarrow> uint256"
definition empty_storage :: storage where
"empty_storage x = 0"

record variable_env =
  venv_stack :: "uint256 list"
  venv_memory :: memory_state
  venv_storage :: storage
  venv_prg_sfx :: program
  venv_balance :: "address \<Rightarrow> uint256"
  venv_caller :: address
  venv_value_sent :: uint256

definition update_balance :: "address => uint256 => (address => uint256) => (address => uint256)"
where "update_balance = undefined"

record constant_env =
  cenv_program :: program
  cenv_this :: address

datatype instruction_result =
  InstructionContinue variable_env
| InstructionToWorld contract_action "variable_env option"

definition instruction_failure_result :: instruction_result
where "instruction_failure_result =
  InstructionToWorld ContractFail None"
  
definition venv_advance_pc :: "variable_env \<Rightarrow> variable_env" where
"venv_advance_pc v =
    v\<lparr>venv_prg_sfx := tl (venv_prg_sfx v)\<rparr>
"
  
definition stack_0_1_op :: "variable_env \<Rightarrow> uint256 \<Rightarrow> instruction_result"
where 
"stack_0_1_op v w =
  InstructionContinue
    (venv_advance_pc (v \<lparr> venv_stack := w # (venv_stack v)\<rparr>))"

definition venv_stack_top :: "variable_env \<Rightarrow> uint256 option" where
"venv_stack_top v =
  (case (venv_stack v) of
    h # _ => Some h
  | _ => None)
  "

definition venv_first_instruction :: "variable_env \<Rightarrow> instruction option"
where
"venv_first_instruction v = (case venv_prg_sfx v of
   [] \<Rightarrow> None
   | h # t \<Rightarrow> Some h
)"

definition venv_pop_stack :: "nat \<Rightarrow> variable_env \<Rightarrow> variable_env" where
"venv_pop_stack n v =
     v\<lparr> venv_stack := drop n (venv_stack v)\<rparr>"

definition venv_change_sfx :: "nat \<Rightarrow> variable_env \<Rightarrow> constant_env \<Rightarrow> variable_env"
where
"venv_change_sfx pos v c =
  v\<lparr>
    venv_prg_sfx := drop_bytes (cenv_program c) pos
  \<rparr>"


definition jump :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction_result"
where "jump v c =
  (case venv_stack_top v of
    None => instruction_failure_result
  | Some pos =>
    (let v_new = venv_change_sfx (unat pos) (venv_pop_stack 1 v) c in
    (case venv_first_instruction v_new of
     Some JUMPDEST =>
           InstructionContinue v_new
    | _ => instruction_failure_result
    )
  ))"

  
fun instruction_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> instruction \<Rightarrow> instruction_result"
where
  "instruction_sem v c (PUSH1 w) = stack_0_1_op v (ucast w)"
| "instruction_sem v c JUMP = jump v c"

datatype program_result =
  ProgramStepRunOut
| ProgramToWorld contract_action storage (* updated storage *)
                 "address => uint256" (* updated balance *)
                 "variable_env option" (* to be pushed in the call stack *)

record account_state =
  account_address :: address
  account_storage :: storage
  account_code :: program
  account_ongoing_calls :: "variable_env list"

fun update_account_state :: "account_state \<Rightarrow> variable_env option \<Rightarrow> account_state"
where
  "update_account_state prev None = prev"
| "update_account_state prev (Some pushed) =
    prev\<lparr> account_storage := venv_storage pushed\<rparr>
        \<lparr> account_ongoing_calls := pushed # account_ongoing_calls prev
        \<rparr>"

definition build_cenv :: "account_state \<Rightarrow> constant_env" where
"build_cenv a = \<lparr>
      cenv_program = (account_code a),
      cenv_this = (account_address a)
   \<rparr>"

definition build_venv_called :: "account_state \<Rightarrow> call_env \<Rightarrow> variable_env" where
"build_venv_called a env =
  \<lparr>
      venv_stack = [],
      venv_memory = empty_memory,
      venv_storage = (account_storage a),
      venv_prg_sfx = (account_code a),
      venv_balance = (callenv_balance env),
      venv_caller = (callenv_caller env),
      venv_value_sent = (callenv_value env)
  \<rparr>
"

fun program_sem :: "variable_env \<Rightarrow> constant_env \<Rightarrow> nat \<Rightarrow> program_result"
where
  "program_sem v c 0 = ProgramStepRunOut"
| "program_sem v c (Suc remaining_steps) =
     (case venv_prg_sfx v of
        [] \<Rightarrow> ProgramToWorld ContractFail (venv_storage v) (venv_balance v) None
      | i # _ \<Rightarrow>
        (case instruction_sem v c i of
          InstructionContinue new_v =>
          program_sem new_v c remaining_steps
        | InstructionToWorld a opt_pushed_v =>
          ProgramToWorld a (venv_storage v) (venv_balance v) opt_pushed_v         
        )
     )"

definition program_result_approximate :: "program_result \<Rightarrow> program_result \<Rightarrow> bool"
where
"program_result_approximate a b
=
  (a = ProgramStepRunOut \<or> a = b)"

(* stuck around here *)
(* try: coinductive mutual definition *)

(* this approach does not work well *)
(* maybe, define a bytecode_run (something similar to specification_run) *)

coinductive respond_to_call_correctly ::
  "(call_env => contract_behavior) =>
       account_state =>
       bool"
   and
   account_state_responds_to_world ::
  "account_state => responce_to_world => bool"
where
  ASR : "respond_to_call_correctly c a \<Longrightarrow>
       (* two other conditions missing *)
       (account_state_responds_to_world a (Respond c(* r f *)))"
| RCC : "(\<forall> (callenv :: call_env)
          (act :: contract_action) (continuation :: responce_to_world).
          c callenv = ContractAction act continuation -->
          (\<exists> pushed_venv st bal.
            (\<forall> steps. program_result_approximate
             (program_sem (build_venv_called a callenv)
                          (build_cenv a) steps)
             (ProgramToWorld act st bal pushed_venv)) \<and>
            (account_state_responds_to_world
                ((update_account_state a pushed_venv)\<lparr>account_storage := st\<rparr>)
                                          continuation)))
                                          \<Longrightarrow> respond_to_call_correctly c a"

definition "example0_program =
    (PUSH1 0 #
       JUMP # [])"

definition "example0_address" :: address where
"example0_address = undefined"
                                          
definition "example0_account_state =
    \<lparr> account_address = example0_address,
       account_storage = empty_storage,
       account_code = example0_program,
       account_ongoing_calls = [] \<rparr>"

definition spec_example_0 :: responce_to_world where
"spec_example_0 =
    Respond
      (\<lambda> _. always_fail)
     (* (\<lambda> _. always_fail)
      always_fai *)"

                                          
theorem example0_spec_impl_match:
    "account_state_responds_to_world
      example0_account_state spec_example_0"
apply(simp add: spec_example_0_def)
apply(coinduction rule: respond_to_call_correctly_account_state_responds_to_world.intros)

end
