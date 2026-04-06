theory Recon_B002_009
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "thf(s_type, type, s: list_int).\nthf(zf_stmt_0, negated_conjecture, (( s ) != ( s )),\n  inference('cnf.neg', [status(esa)], [conj_0])).\nthf(zip_derived_cl32, plain, (((s) != (s))),\n    inference('cnf', [status(esa)], [zf_stmt_0])).\nthf(zip_derived_cl35, plain, ($false),\n    inference('simplify', [status(thm)], [zip_derived_cl32])).\n"
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