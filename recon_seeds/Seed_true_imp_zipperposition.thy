theory Seed_true_imp_zipperposition
imports Main
begin

lemma true_imp: "True \<longrightarrow> True"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end