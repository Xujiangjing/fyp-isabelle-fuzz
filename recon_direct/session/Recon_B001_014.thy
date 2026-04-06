theory Recon_B001_014
imports Main
begin

(* Direct TSTP formula parser fuzzing — auto-generated *)
(* Target: ATP_Proof.parse_fol_formula *)

ML \<open>
  let
    val proof_text = "% SZS status Theorem for problem\n% SZS output start Proof for problem\nfof(f1, conjecture, ![X]: (f84(X, zero) = X),\n    file('problem.p', conjecture)).\nfof(f2, negated_conjecture, ~(![X]: (f84(X, zero) = X)),\n    inference(negated_conjecture, [], [f1])).\nfof(f3, negated_conjecture, ~(f84(sk1, zero) = sk1),\n    inference(skolemisation, [status(esa), new_symbols(skolem, [sk1])], [f2])).\nfof(f4, axiom, ![X]: (f84(X, zero) = X),\n    file('problem.p', ax_f84_zero)).\nfof(f5, definition, $false,\n    inference(resolution, [status(thm)], [f3, f4])).\n% SZS output end Proof for problem"
    val all_lines = String.tokens (fn c => c = #"\n") proof_text
    val _ = tracing ("[RECON_DIRECT] Parsing " ^
              Int.toString (length all_lines) ^ " lines")

    fun is_formula_line s =
      String.isPrefix "fof(" s orelse String.isPrefix "cnf(" s orelse
      String.isPrefix "thf(" s orelse String.isPrefix "tff(" s

    val formula_lines = List.filter is_formula_line all_lines
    val _ = tracing ("[RECON_DIRECT] Found " ^
              Int.toString (length formula_lines) ^ " formula lines")

    fun try_parse_line line =
      let
        val syms = raw_explode line
      in
        (let
           val (id, _) = ATP_Proof.scan_general_id syms
           val _ = tracing ("[RECON_DIRECT] Scanned ID: " ^ id)
         in () end
         handle Fail msg =>
           tracing ("[RECON_DIRECT] scan Fail: " ^ msg)
         | Match => tracing "[RECON_DIRECT] scan Match"
         | ATP_Proof.UNRECOGNIZED_ATP_PROOF () =>
           tracing "[RECON_DIRECT] scan UNRECOGNIZED");
        (let
           val (_, _) = ATP_Proof.parse_fol_formula syms
           val _ = tracing "[RECON_DIRECT] parse_fol_formula OK"
         in () end
         handle Fail msg =>
           tracing ("[RECON_DIRECT] parse Fail: " ^ msg)
         | Match =>
           tracing "[RECON_DIRECT] parse Match"
         | ATP_Proof.UNRECOGNIZED_ATP_PROOF () =>
           tracing "[RECON_DIRECT] parse UNRECOGNIZED"
         | ERROR msg =>
           tracing ("[RECON_DIRECT] parse ERROR: " ^ msg))
      end
  in
    List.app try_parse_line formula_lines;
    tracing "[RECON_DIRECT] All formulas processed — no crash"
  end
  handle
    Fail msg =>
      tracing ("[RECON_DIRECT] TOP Fail: " ^ msg)
  | Match =>
      tracing "[RECON_DIRECT] TOP Match"
  | ATP_Proof.UNRECOGNIZED_ATP_PROOF () =>
      tracing "[RECON_DIRECT] TOP UNRECOGNIZED_ATP_PROOF"
  | ERROR msg =>
      tracing ("[RECON_DIRECT] TOP ERROR: " ^ msg)
  | Overflow =>
      tracing "[RECON_DIRECT] TOP Overflow"
  | Subscript =>
      tracing "[RECON_DIRECT] TOP Subscript"
  | Size =>
      tracing "[RECON_DIRECT] TOP Size"
\<close>

end