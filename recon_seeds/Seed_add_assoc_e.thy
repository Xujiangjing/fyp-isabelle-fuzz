theory Seed_add_assoc_e
imports Main
begin

lemma add_assoc: "(x::nat) + (y + z) = (x + y) + z"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end