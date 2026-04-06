theory Seed_distrib_zipperposition
imports Main
begin

lemma distrib: "(x::nat) * (y + z) = x * y + x * z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end