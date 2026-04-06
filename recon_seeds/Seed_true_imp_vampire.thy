theory Seed_true_imp_vampire
imports Main
begin

lemma true_imp: "True \<longrightarrow> True"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end