theory Seed_eq_or_false_e
imports Main
begin

lemma eq_or_false: "(x::nat) = x \<or> False"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end