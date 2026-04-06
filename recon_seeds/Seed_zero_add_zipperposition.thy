theory Seed_zero_add_zipperposition
imports Main
begin

lemma zero_add: "(0::nat) + x = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end