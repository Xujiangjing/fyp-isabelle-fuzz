theory Recon_0109
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% SZS status Theorem for problem\n% SZS output start CNFRefutation for problem\nfof(c_0_0, axiom, ![X,Y]: (f66(X,Y) = f66(Y,X)),\n    unknown).\nfof(c_0_1, axiom, ![X]: (f66(X, zero) = X),\n    unknown).\nfof(c_0_2, axiom, ![X,Y,Z]: (f66(f66(X,Y),Z) = f66(X,f66(Y,Z))),\n    unknown).\nfof(c_0_3, negated_conjecture, ~(![X,Y]: (f66(X,Y) = f66(Y,X))),\n    inference(assume_negation, [status(cth)], [goal])).\nfof(c_9545_71, negated_conjecture, ~(f66(sk1, sK1198) = f66(sK1198, sk1)),\n    inference(skolemize, [status(esa)], [c_0_3])).\ncnf(c_0_5, axiom, f66(X,Y) = f66(Y,X),\n    inference(fof_to_cnf, [status(thm)], [c_0_0])).\ncnf(c_0_6, plain, $false,\n    inference(sr, [status(thm)], [c_0_4, c_0_5])).\n% SZS output end CNFRefutation for problem"
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