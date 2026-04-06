theory Seed_min_le_zipperposition
imports Main
begin

lemma min_le: "min (x::nat) y \<le> x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end