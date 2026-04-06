theory Seed_rev_rev_e
imports Main
begin

lemma rev_rev: "rev (rev xs) = (xs::nat list)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end