theory Seed_eq_or_false_vampire
imports Main
begin

lemma eq_or_false: "(x::nat) = x \<or> False"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end