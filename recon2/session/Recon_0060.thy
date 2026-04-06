theory Recon_0060
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% SZS status Theorem for problem\n% SZS output start CNFRefutation for problem\nfof(c_0_0, negated_conjecture, ~(![X]: (plus(X, c25) = X)),\n    inference(assume_negation, [status(cth)], [goal])).\nfof(c_0_1, negated_conjecture, ~(plus(sk1, c25) = sk1),\n    inference(skolemize, [status(esa)], [c_0_0])).\ncnf(c_0_2, axiom, plus(X, c25) = X,\n    file('problem.p', ax_plus_c25)).\ncnf(c_0_3, plain, $false,\n    inference(rw, [status(thm)], [c_0_1, c_0_2])).\ncnf(c_0_2, axiom, plus(X, c25) = X,\n    file('problem.p', ax_plus_c25)).\n% SZS output end CNFRefutation for problem"
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