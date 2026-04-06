theory Recon_B002_011
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "# Preprocessing class: HSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)\n# Starting new_ho_10 with 5s (1) cores\n# new_ho_10 with pid 51054 completed with status 0\n# Result found by new_ho_10\n# Preprocessing class: HSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)\n# Starting new_ho_10 with 5s (1) cores\n# No SInE strategy applied\n# Search class: HUHPF-FFSF00-SFFFFFNN\n# Scheduled 2 strats onto 1 cores with 5 seconds (5 total)\n# Starting new_ho_10 with 4s (1) cores\n# new_ho_10 with pid 51055 completed with status 0\n# Result found by new_ho_10\n# Preprocessing class: HSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 5 seconds (5 total)\n# Starting new_ho_10 with 5s (1) cores\n# No SInE strategy applied\n# Search class: HUHPF-FFSF00-SFFFFFNN\n# Scheduled 2 strats onto 1 cores with 5 seconds (5 total)\n# Starting new_ho_10 with 4s (1) cores\n# Initializing proof state\n# Scanning for AC axioms\n## Presaturation interreduction done\n\n# Proof found!\n# SZS status Theorem\n# SZS output start CNFRefutation\nthf(decl_sort1, type, list_int: $tType).\nthf(decl_22, type, s: list_int).\nthf(conj_0, conjecture, ((s)=(s)), file('/Users/xujiangjing/fyp-isabelle-fuzz/unique_inputs/0001_r001_20260331_221018_prob_zipperposition_min_1.p', conj_0)).\nthf(c_0_1, negated_conjecture, ((s)!=(s)), inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])])).\nthf(c_0_2, negated_conjecture, ((s)!=(s)), inference(fof_nnf,[status(thm)],[c_0_1])).\nthf(c_0_3, negated_conjecture, ((s)!=(s)), inference(split_conjunct,[status(thm)],[c_0_2])).\nthf(c_0_4, negated_conjecture, ($false), inference(cn,[status(thm)],[c_0_3]), ['proof']).\n# SZS output end CNFRefutation\n"
    (* Phase 1: extract_tstplike_proof_and_outcome — NO exception handler,
       so any unexpected exception will crash the theory and appear in build log *)
    val (proof_body, outcome) =
      ATP_Proof.extract_tstplike_proof_and_outcome true [] [] proof_text
    (* Phase 2: tokenize and parse individual formula lines *)
    val tokens = String.tokens (fn c => c = #"\n") proof_body
    fun is_formula_line s =
      String.isPrefix "fof(" s orelse String.isPrefix "cnf(" s orelse
      String.isPrefix "thf(" s orelse String.isPrefix "tff(" s
    val formula_lines = List.filter is_formula_line tokens
    (* Phase 3: call parse_fol_formula on each formula line *)
    val _ = List.app (fn line =>
      let
        val syms = raw_explode line
        val _ = ATP_Proof.parse_fol_formula syms
      in () end
      handle Fail _ => ()  (* expected for malformed input *)
      | ATP_Proof.UNRECOGNIZED_ATP_PROOF () => ()  (* expected *)
      ) formula_lines
  in () end
\<close>

end