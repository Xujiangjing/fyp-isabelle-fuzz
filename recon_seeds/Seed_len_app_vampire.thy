theory Seed_len_app_vampire
imports Main
begin

lemma len_app: "length (xs @ ys) = length xs + length (ys::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end