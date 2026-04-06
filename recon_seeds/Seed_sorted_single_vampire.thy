theory Seed_sorted_single_vampire
imports Main
begin

lemma sorted_single: "sorted [x] = True"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end