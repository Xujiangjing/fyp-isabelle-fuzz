theory Recon_B005_002
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% done 35 iterations in 0.065s\n% SZS status Error for '/Users/xujiangjing/fyp-isabelle-fuzz/unique_inputs/0004_r003_20260331_221053_prob_zipperposition_1.p'\n% SZS output start Refutation\nthf(list_list_int_type, type, list_list_int: $tType).\nthf(list_int_type, type, list_int: $tType).\nthf(cons_list_int_type, type, cons_list_int: list_int > list_list_int > list_list_int).\nthf(n0_type, type, n0: list_int).\nthf(rev_list_int_type, type, rev_list_int: list_list_int > list_list_int).\nthf(nil_list_int_type, type, nil_list_int: list_list_int).\nthf(conj_0, conjecture,\n  (( rev_list_int @ ( cons_list_int @ n0 @ nil_list_int ) ) =\n   ( cons_list_int @ n0 @ nil_list_int ))).\nthf(zf_stmt_0, negated_conjecture,\n  (( rev_list_int @ ( cons_list_int @ n0 @ nil_list_int ) ) !=\n   ( cons_list_int @ n0 @ nil_list_int )),\n  inference('cnf.neg', [status(esa)], [conj_0])).\nthf(zip_derived_cl1454, plain,\n    (((rev_list_int @ (cons_list_int @ n0 @ nil_list_int))\n       != (cons_list_int @ n0 @ nil_list_int))),\n    inference('cnf', [status(esa)], [zf_stmt_0])).\nthf(fact_2_rev__singleton__conv, axiom,\n  (![Xs:list_list_int,X:list_int]:\n   ( ( ( rev_list_int @ Xs ) = ( cons_list_int @ X @ nil_list_int ) ) <=>\n     ( ( Xs ) = ( cons_list_int @ X @ nil_list_int ) ) ))).\nthf(zip_derived_cl5, plain,\n    (![X0 : list_int, X1 : list_list_int]:\n       (((rev_list_int @ X1) = (cons_list_int @ X0 @ nil_list_int))\n        | ((X1) != (cons_list_int @ X0 @ nil_list_int)))),\n    inference('cnf', [status(esa)], [fact_2_rev__singleton__conv])).\nthf(zip_derived_cl1486, plain,\n    (((cons_list_int @ n0 @ nil_list_int)\n       != (cons_list_int @ n0 @ nil_list_int))),\n    inference('demod', [status(thm)],\n              [zip_derived_cl1454, zip_derived_cl1485])).\nfof(injected_2870, plain, $true, inference(, [status(thm)], [])).\nthf(zip_derived_cl1487, plain, ($false),\n    inference('simplify', [status(thm)], [zip_derived_cl1486])).\n\n% SZS output end Refutation\n"
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