theory Seed_rev_rev_vampire
imports Main
begin

lemma rev_rev: "rev (rev xs) = (xs::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end