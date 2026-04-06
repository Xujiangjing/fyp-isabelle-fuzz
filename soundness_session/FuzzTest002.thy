theory FuzzTest002
imports Main
begin

lemma false_1: "True = False"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_2: "(y::nat) < y + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_3: "(x::nat) < x + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_4: "(y::nat) \<in> set [y, z]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_5: "(0::nat) = Suc 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_6: "(y::nat) + m = m + y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end