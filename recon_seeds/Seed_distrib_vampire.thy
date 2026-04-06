theory Seed_distrib_vampire
imports Main
begin

lemma distrib: "(x::nat) * (y + z) = x * y + x * z"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end