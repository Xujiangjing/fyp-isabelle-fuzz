theory Seed_add_zero_e
imports Main
begin

lemma add_zero: "(x::nat) + 0 = x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end