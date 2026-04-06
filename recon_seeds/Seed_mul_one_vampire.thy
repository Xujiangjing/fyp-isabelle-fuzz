theory Seed_mul_one_vampire
imports Main
begin

lemma mul_one: "(x::nat) * 1 = x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end