(* Loaded into the interactive HOL session used while developing proofs. *)
val _ = app load ["panQsortProofTheory", "panContractLib", "panStepLib", "blastLib"];
open panQsortProgTheory panQsortSpecTheory panLogicTheory panQsortProofTheory
     panStepLib panSemTheory;
val _ = set_trace "Goalstack.print_goal_at_top" 0;
val _ = show_assums := true;
val decls = rhs (concl panQsortProgTheory.qsort_decls_def);
val contracts = panContractLib.contracts_of decls;
fun goal_of name =
  panContractLib.fun_spec_goal “qsort_code” (panContractLib.find_contract contracts name);
val st = “s : (64, word64 list) panSem$state”;
fun loop name i =
  panStepLib.loop_contract_at
    (List.nth (#loops (panContractLib.find_contract contracts name), i)) st;
fun ngoals () = print ("goals left: " ^ Int.toString (length (top_goals())) ^ "\n");
