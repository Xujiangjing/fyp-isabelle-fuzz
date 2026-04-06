theory Recon_0116
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% SZS status Satisfiable for problem\n% SZS output start CNFRefutation for problem\nfof(c_0_0, axiom, ![X,Y]: (f46(X,Y) = f46(Y,X)),\n    file('problem.p', f46_comm)).\nfof(extra_6022, axiom, (![X,Y]: (X = Y))).\nfof(c_0_1, axiom, ![X]: (f46(X, c96) = X),\n    file('problem.p', f46_c96)).\nfof(c_0_2, axiom, ![X,Y,Z]: (f46(f46(X,Y),Z) = f46(X,f46(Y,Z))),\n    file('problem.p', f46_assoc)).\nfof(c_0_3, negated_conjecture, ~(![X,Y]: (f46(X,Y) = f46(Y,X))),\n    inference(assume_negation, [status(cth)], [goal])).\nfof(c_0_4, negated_conjecture, ~(f46(sK906, sk2) = f46(sk2, sK906)),\n    inference(skolemize, [status(esa)], [c_0_3])).\ncnf(c_0_5, axiom, f46(X,Y) = f46(Y,X),\n    inference(fof_to_cnf, [status(thm)], [c_9989_21])).\ncnf(c_0_6, plain, $false,\n    inference(sr, [status(thm)], [c_0_4, c_0_5])).\n% SZS output end CNFRefutation for problem"
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