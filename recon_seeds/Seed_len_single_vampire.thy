theory Seed_len_single_vampire
imports Main
begin

lemma len_single: "length [(x::nat)] = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end