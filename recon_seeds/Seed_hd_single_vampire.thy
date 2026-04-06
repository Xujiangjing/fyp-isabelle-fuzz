theory Seed_hd_single_vampire
imports Main
begin

lemma hd_single: "hd [x] = (x::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end