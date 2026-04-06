theory Seed_hd_single_zipperposition
imports Main
begin

lemma hd_single: "hd [x] = (x::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end