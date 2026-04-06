theory Recon_B001_003
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% /Applications/Isabelle2025-2.app/contrib/zipperposition-2.1-1/x86_64-darwin/zipperposition --input tptp --output tptp --timeout 30.000 --mode=ho-pragmatic --tptp-def-as-rewrite --rewrite-before-cnf=true --max-inferences=1 --ho-unif-max-depth=1 --ho-max-elims=0 --ho-max-app-projections=0 --ho-max-rigid-imitations=1 --ho-max-identifications=0 --boolean-reasoning=bool-hoist --bool-hoist-simpl=true --bool-select=LI --recognize-injectivity=true --ext-rules=ext-family --ext-rules-max-depth=1 --ho-choice-inst=true --ho-prim-enum=none --ho-elim-leibniz=0 --interpret-bool-funs=true --try-e='$E_HOME/eprover' --tmp-dir='$ISABELLE_TMP_PREFIX' --ho-unif-level=pragmatic-framework --select=bb+e-selection2 --post-cnf-lambda-lifting=true -q '4|prefer-sos|pnrefined(2,1,1,1,2,2,2)' -q '6|prefer-processed|conjecture-relative-struct(1.5,3.5,2,3)' -q '1|const|fifo' -q '4|prefer-ground|orient-lmax(2,1,2,1,1)' -q '4|defer-sos|conjecture-relative-struct(1,5,2,3)' --avatar=off --recognize-injectivity=true --ho-neg-ext=true --e-timeout=2 --ho-pattern-decider=true --ho-fixpoint-decider=true --e-max-derived=50 --ignore-orphans=true --e-auto=true --presaturate=true --e-call-point=0.1 /Users/xujiangjing/.isabelle/Isabelle2025-2/prob_zipperposition_1.p\n% 2026-04-03 00:08:58.875\nparse error: expected declaration\n    at file '/Users/xujiangjing/.isabelle/Isabelle2025-2/prob_zipperposition_1.p': line 9, co/**/l 4 to 7"
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