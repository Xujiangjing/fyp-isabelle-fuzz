theory Recon_0134
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% SZS status BROKEN_STATUS for problem\n% SZS output start CNFRefutation for problem\nfof(c_0_0, negated_conjecture, ~(![X]: (f62(X, zero) = X)),\n    inference(assume_negation, [status(cth)], [goal])).\nfof(c_0_1, negated_conjecture, ~(f62(sk1, zero) = sk1),\n    inference(skolemize, [status(esa)], [c_0_0])).\ncnf(c_0_2, axiom, f62(X, zero) = X,\n    file('problem.p', ax_f62_zero)).\ncnf(c_0_3, plain, $false,\n    inference(rw, [status(thm)], [c_0_1, c_0_2])).\n% SZS output end CNFRefutation for problem"
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