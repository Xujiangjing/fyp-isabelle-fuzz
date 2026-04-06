theory Seed_sorted_single_e
imports Main
begin

lemma sorted_single: "sorted [x] = True"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end