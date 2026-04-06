theory Seed_add_zero_vampire
imports Main
begin

lemma add_zero: "(x::nat) + 0 = x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end