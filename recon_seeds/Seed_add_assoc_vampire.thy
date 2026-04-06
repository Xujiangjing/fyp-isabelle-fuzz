theory Seed_add_assoc_vampire
imports Main
begin

lemma add_assoc: "(x::nat) + (y + z) = (x + y) + z"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end