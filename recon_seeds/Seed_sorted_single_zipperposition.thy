theory Seed_sorted_single_zipperposition
imports Main
begin

lemma sorted_single: "sorted [x] = True"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end