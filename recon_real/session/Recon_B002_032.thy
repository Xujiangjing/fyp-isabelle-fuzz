theory Recon_B002_032
imports Main
begin

(* Fuzzing INBOUND proof reconstruction — auto-generated *)
(* Target: atp_proof.ML TSTP parser *)
(* Prover simulated: e *)

ML \<open>
  let
    val proof_text = "% /opt/homebrew/bin/eprover --tstp-in --tstp-out --silent --auto-schedule --cpu-limit=2 --proof-object=1 /Users/xujiangjing/.isabelle/Isabelle2025/prob_e_min_1.p\n% 2026-04-04 13:22:07.834\n# Preprocessing class: FSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 2s (1) cores\n# G-E--_302_C18_F1_URBAN_RG_S04BN with pid 45973 completed with status 1\n# Result found by G-E--_302_C18_F1_URBAN_RG_S04BN\n# Preprocessing class: FSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 2s (1) cores\n# No SInE strategy applied\n# Search class: FUUPF-FFSF22-SFFFFFNN\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting SAT001_MinMin_p005000_rr_RG with 2s (1) cores\n# SAT001_MinMin_p005000_rr_RG with pid 45974 completed with status 1\n# Result found by SAT001_MinMin_p005000_rr_RG\n# Preprocessing class: FSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 2s (1) cores\n# No SInE strategy applied\n# Search class: FUUPF-FFSF22-SFFFFFNN\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting SAT001_MinMin_p005000_rr_RG with 2s (1) cores\n# Presaturation interreduction done\n\n# No proof found!\n# SZS status CounterSatisfiable\n# SZS output start Saturation\ntff(decl_sort1, type, nat: $tType).\ntff(decl_23, type, plus_plus_nat: (nat * nat) > nat).\ntff(decl_24, type, zero_zero_nat: nat).\nfof(extra_3029, axiom, (![X,Y]: (X = Y))).\n$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$$\ntff(decl_25, type, x: nat).\ntff(conj_0, conjecture, plus_plus_nat(zero_zero_nat,x)=x, file('/Users/xujiangjing/.isabelle/Isabelle2025/prob_e_min_1.p', conj_0)).\ntff(c_0_1, negated_conjecture, plus_plus_nat(zero_zero_nat,x)!=x, inference(fof_simplification,[status(thm)],[inference(assume_negation,[status(cth)],[conj_0])])).\ntff(c_0_2, negated_conjecture, plus_plus_nat(zero_zero_nat,x)!=x, inference(fof_nnf,[status(thm)],[c_0_1])).\ntcf(c_0_3, negated_conjecture, plus_plus_nat(zero_zero_nat,x)!=x, inference(split_conjunct,[status(thm)],[c_0_2]), ['final']).\n# SZS output end Saturation% /opt/homebrew/bin/eprover --tstp-in --tstp-out --silent --auto-schedule --cpu-limit!=2 --proof-object!=1 /Users/xujiangjing/.isabelle/Isabelle2025/prob_e_min_1.p\n% 2026-04-04 13:22:07.834\n# Preprocessing class: FSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 2s (1) cores\n# G-E--_302_C18_F1_URBAN_RG_S04BN with pid 45973 completed with status 1\n# Result found by G-E--_302_C18_F1_URBAN_RG_S04BN\n# Preprocessing class: FSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 2s (1) cores\n# No SInE strategy applied\n# Search class: FUUPF-FFSF22-SFFFFFNN\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting SAT001_MinMin_p005000_rr_RG with 2s (1) cores\n# SAT001_MinMin_p005000_rr_RG with pid 45974 completed with status 1\n# Result found by SAT001_MinMin_p005000_rr_RG\n# Preprocessing class: FSSSSMSSSSSNFFN.\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting G-E--_302_C18_F1_URBAN_RG_S04BN with 2s (1) cores\n# No SInE strategy applied\n# Search class: FUUPF-FFSF22-SFFFFFNN\n# Scheduled 1 strats onto 1 cores with 2 seconds (2 total)\n# Starting SAT001_MinMin_p005000_rr_RG with 2s (1) cores\n# Presaturation interreduction done\n\n# No proof found!\n# SZS status CounterSatisfiable\n# SZS output start Saturation\ntff(decl_sort1, type, nat: $tType).\n"
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