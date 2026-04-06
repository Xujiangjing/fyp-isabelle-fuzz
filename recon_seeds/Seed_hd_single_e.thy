theory Seed_hd_single_e
imports Main
begin

lemma hd_single: "hd [x] = (x::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end