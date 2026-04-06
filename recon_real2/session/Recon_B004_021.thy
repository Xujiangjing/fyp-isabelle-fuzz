theory Recon_B004_021
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% done 0 iterations in 0.002s\n% SZS status Theorem for '/Users/xujiangjing/fyp-isabelle-fuzz/unique_inputs/0023_round007_20260331_202046_prob_zipperposition_min_1.p'\n% SZS output start Refutation\nthf(a_type, type, a: $tType).\nthf(plus_plus_a_type, type, plus_plus_a: a > a > a).\nthf(m_type, type, m: a).\nthf(one_one_a_type, type, one_one_a: a).\nthf(conj_0, conjecture,\n  (( plus_plus_a @ m @ one_one_a ) = ( plus_plus_a @ m @ one_one_a ))).\nthf(zf_stmt_0, definition,\n  (( plus_plus_a @ m @ one_one_a ) != ( plus_plus_a @ m @ one_one_a )),\n  inference('cnf.neg', [status(esa)], [conj_0])).\nthf(zip_derived_cl0, plain,\n    (((plus_plus_a @ m @ one_one_a) != (plus_plus_a @ m @ one_one_a))),\n    inference('cnf', [status(esa)], [zf_stmt_0])).\nthf(zip_derived_cl1, plain, ($false),\n    inference('simplify', [status(thm)], [zip_derived_cl0])).\n\n% SZS output end Refutation\n"
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