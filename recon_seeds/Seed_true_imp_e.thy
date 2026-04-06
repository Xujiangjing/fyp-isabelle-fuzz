theory Seed_true_imp_e
imports Main
begin

lemma true_imp: "True \<longrightarrow> True"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end