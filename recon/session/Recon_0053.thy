theory Recon_0053
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% SZS status Theorem for problem\n% SZS output start Proof for problem\nthf(ty_nat, type, nat: $tType).\nthf(ty_f12, type, f12: nat > nat > nat).\nthf(ty_zero, type, zero: nat).\ninclude('evil.ax').\nfof(extra_2863, negated_conjecture, ($false)).\nthf(ax1, axiom, ![X: nat]: (f12 @ X @ zero) = X).\nthf(conj, conjecture, ![X: nat]: (f12 @ X @ zero) = X).\nthf(neg, negated_conjecture, ~(![X: nat]: (f12 @ X @ zero) = X),\n    inference(skolemize, [status(cth)], [conj])).\nthf(result, plain, $false,\n    inference(superposition, [status(thm)], [neg, ax1])).\n% SZS output end Proof for problem"
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