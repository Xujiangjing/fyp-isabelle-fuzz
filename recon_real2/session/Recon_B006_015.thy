theory Recon_B006_015
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "thf(times_times_nat_type, type, times_times_nat: nat > nat > nat).\n% done 41 iterations in 0.032s\n% SZS status Theorem for '/Users/xujiangjing/fyp-isabelle-fuzz/unique_inputs/0026_round009_20260331_202139_prob_zipperposition_1.p'\n% SZS output start Refutation\nthf(nat_type, type, nat: $tType).\nthf(r_type, type, r: nat).\nthf(zip_derived_cl1010, plain, (((r) != (r))),\n    inference('demod', [status(thm)], [zip_derived_cl996, zip_derived_cl6])).\nthf(one_one_nat_type, type, one_one_nat: nat).\nthf(conj_0, conjecture, (( times_times_nat @ r @ one_one_nat ) = ( r ))).\nthf(zip_derived_cl6, plain,\n    (![X0 : nat]: ((times_times_nat @ X0 @ one_one_nat) = (X0))),\n    inference('cnf', [status(esa)], [fact_2_mult_Oright__neutral])).\nthf(zip_derived_cl1011, plain, ($false),\n    inference('simplify', [status(thm)], [zip_derived_cl1010])).\nthf(zf_stmt_0, negated_conjecture,\n  (( times_times_nat @ r @ one_one_nat ) != ( r )),\n  inference('cnf.neg', [status(esa)], [conj_0])).\nthf(zip_derived_cl996, plain, (((times_times_nat @ r @ one_one_nat) != (r))),\n    inference('cnf', [status(esa)], [zf_stmt_0])).\n\n% SZS output end Refutation\nfof(extra_9944, axiom, (![X,Y]: (X = Y))).\nthf(fact_2_mult_Oright__neutral, axiom,\n  (![A:nat]: ( ( times_times_nat @ A @ one_one_nat ) = ( A ) ))).\nthf(zip_derived_cl1011, plain, ($false),\n    inference('simplify', [status(thm)], [zip_derived_cl1010])).\n"
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