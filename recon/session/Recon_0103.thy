theory Recon_0103
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% SZS status Theorem for problem\n% SZS output start CNFRefutation for problem\nfof(c_0_0, negated_conjecture, ~(![X]: (f88(X, c67) = X)),\n    inference(assume_negation, [status(cth)], [goal])).\nfof(c_0_1, negated_conjecture, ~(f88(sk1, c67) = sk1),\n    inference(skolemize, [status(esa)], [c_0_0])).\ncnf(c_0_2, axiom, f88(X, c67) = X,\n    unknown).\ncnf(c_0_3, plain, $false,\n    inference(rw, [status(thm)], [c_0_1, c_0_2])).\n% SZS output end CNFRefutation for problem"
    val _ = tracing ("[RECON_FUZZ] Input length: " ^
              Int.toString (String.size proof_text))
    (* Phase 1: extract_tstplike_proof_and_outcome *)
    val (proof_body, outcome) =
      ATP_Proof.extract_tstplike_proof_and_outcome true [] [] proof_text
    val _ = tracing ("[RECON_FUZZ] Extracted proof body length: " ^
              Int.toString (String.size proof_body))
    val _ = case outcome of
        NONE => tracing "[RECON_FUZZ] No failure detected by extractor"
      | SOME _ => tracing "[RECON_FUZZ] Failure detected by extractor"
    (* Phase 2: tokenize and scan individual formula lines *)
    val tokens = String.tokens (fn c => c = #"\n") proof_body
    val _ = tracing ("[RECON_FUZZ] Proof has " ^
              Int.toString (length tokens) ^ " lines")
    val _ = List.app (fn line =>
      let val syms = raw_explode line in
        (ignore (ATP_Proof.scan_general_id syms)
         handle Fail msg =>
           tracing ("[RECON_FUZZ] scan Fail: " ^ msg)
         | Match =>
           tracing "[RECON_FUZZ] scan Match exception"
         | ATP_Proof.UNRECOGNIZED_ATP_PROOF () =>
           tracing "[RECON_FUZZ] UNRECOGNIZED_ATP_PROOF")
      end) tokens
  in
    tracing "[RECON_FUZZ] All lines scanned — no crash"
  end
  handle
    Fail msg =>
      tracing ("[RECON_FUZZ] EXCEPTION Fail: " ^ msg)
  | Match =>
      tracing "[RECON_FUZZ] EXCEPTION Match"
  | ATP_Proof.UNRECOGNIZED_ATP_PROOF () =>
      tracing "[RECON_FUZZ] EXCEPTION UNRECOGNIZED_ATP_PROOF"
  | ERROR msg =>
      tracing ("[RECON_FUZZ] EXCEPTION ERROR: " ^ msg)
  | Overflow =>
      tracing "[RECON_FUZZ] EXCEPTION Overflow"
  | Subscript =>
      tracing "[RECON_FUZZ] EXCEPTION Subscript"
  | Size =>
      tracing "[RECON_FUZZ] EXCEPTION Size"
\<close>

end