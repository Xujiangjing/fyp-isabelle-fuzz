theory FuzzTest000
imports Main
begin

lemma true_1: "n + 0 = (n::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_2: "m + 0 = (m::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_3: "Suc (n::nat) = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_4: "Suc (z::nat) = z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma keyword_tff_5: "tff = (tff :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_6: "Suc (b::nat) = b"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_7: "(a::nat) \<le> a"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end