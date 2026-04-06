theory Seed_len_single_zipperposition
imports Main
begin

lemma len_single: "length [(x::nat)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end