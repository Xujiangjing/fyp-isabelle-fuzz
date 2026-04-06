theory Recon_0167
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% SZS status Theorem for problem\n% SZS output start Proof for problem\nthf(ty_nat, type, nat: $tType).\nthf(ty_f19, type, f19: nat > nat > nat).\nthf(ty_c18, type, c18: nat).\nthf(ax1, axiom, ![X: nat]: (f19 @ X @ c18) = X).\nthf(conj, conjecture, ![X: nat]: (f19 @ X @ c18) = X).\nthf(neg, negated_conjecture, ~(![X: nat]: (f19 @ X @ c18) = X),\n    inference(negated_conjecture, [status(cth)], [conj])).\nthf(result, plain, $false,\n    inference(superposition, [status(thm)], [neg, ax1])).\n% SZS output end Proof for problem"
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