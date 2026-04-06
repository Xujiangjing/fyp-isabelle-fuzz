theory Seed_distrib_e
imports Main
begin

lemma distrib: "(x::nat) * (y + z) = x * y + x * z"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end