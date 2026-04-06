theory Seed_mul_one_zipperposition
imports Main
begin

lemma mul_one: "(x::nat) * 1 = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end