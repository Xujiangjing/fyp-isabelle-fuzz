theory Seed_min_le_e
imports Main
begin

lemma min_le: "min (x::nat) y \<le> x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end