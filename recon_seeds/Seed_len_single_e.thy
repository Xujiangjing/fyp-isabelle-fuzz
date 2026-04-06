theory Seed_len_single_e
imports Main
begin

lemma len_single: "length [(x::nat)] = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end