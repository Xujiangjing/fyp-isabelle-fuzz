theory Recon_B000_020
imports Main
begin

(* Direct TSTP formula parser fuzzing — auto-generated *)
(* Target: ATP_Proof.parse_fol_formula *)

ML \<open>
  let
    val proof_text = "% SZS status Theorem for problem\n% SZS output start CNFRefutation for problem\nfof(c_0_0, axiom, ![X,Y]: (f81(X,Y) = f81(Y,X)),\n    unknown).\nfof(c_0_1, axiom, ![X]: (f81(X, zero) = X),\n    unknown).\nfof(c_0_2, axiom, ![X,Y,Z]: (f81(f81(X,Y),Z) = f81(X,f81(Y,Z))),\n    unknown).\nfof(c_0_3, negated_conjecture, ~(![X,Y]: (f81(X,Y) = f81(Y,X))),\n    inference(assume_negation, [status(cth)], [goal])).\nfof(c_0_4, negated_conjecture, ~(f81(sK65, sk2) = f81(sk2, sK65)),\n    inference(skolemize, [status(esa)], [c_0_3])).\ncnf(c_0_5, axiom, f81(X,Y) = f81(Y,X),\n    inference(fof_to_cnf, [status(thm)], [c_0_0])).\ncnf(c_0_6, plain, $false,\n    inference(sr, [status(thm)], [c_0_4, c_0_5])).\n% SZS output end CNFRefutation for problem"
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