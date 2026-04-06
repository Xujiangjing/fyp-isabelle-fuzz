theory Seed_mul_one_e
imports Main
begin

lemma mul_one: "(x::nat) * 1 = x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end