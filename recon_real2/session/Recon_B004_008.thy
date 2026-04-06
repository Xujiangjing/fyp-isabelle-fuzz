theory Recon_B004_008
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% done 71 iterations in 0.079s\n% SZS status Theorem for '/Users/xujiangjing/fyp-isabelle-fuzz/unique_inputs/0002_r002_20260331_221036_prob_zipperposition_1.p'\n% SZS output start Refutation\nthf(option_nat_type, type, option_nat: $tType).\nthf(list_option_nat_type, type, list_option_nat: $tType).\nthf(cons_option_nat_type, type, cons_option_nat: option_nat > list_option_nat > list_option_nat).\nthf(nil_option_nat_type, type, nil_option_nat: list_option_nat).\nthf(r7_type, type, r7: option_nat).\nthf(hd_option_nat_type, type, hd_option_nat: list_option_nat > option_nat).\nthf(conj_0, conjecture,\n  (( hd_option_nat @ ( cons_option_nat @ r7 @ nil_option_nat ) ) = ( r7 ))).\nthf(zf_stmt_0, negated_conjecture,\n  (( hd_option_nat @ ( cons_option_nat @ r7 @ nil_option_nat ) ) != ( r7 )),\n  inference('cnf.neg', [status(esa)], [conj_0])).\nthf(zip_derived_cl1497, plain,\n    (((hd_option_nat @ (cons_option_nat @ r7 @ nil_option_nat)) != (r7))),\n    inference('cnf', [status(esa)], [zf_stmt_0])).\nthf(fact_5_list_Osel_I1_J, axiom,\n  (![X21:option_nat,X22:list_option_nat]:\n   ( ( hd_option_nat @ ( cons_option_nat @ X21 @ X22 ) ) = ( X21 ) ))).\n"
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