theory FuzzTest002
imports Main
begin

lemma true_1: "(y::nat) * 1 = y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_2: "length [w] = (1::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_3: "(z::nat) < z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_4: "(v::nat) < v + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_5: "(n::nat) \<in> set [n, b]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_6: "length ([(1::nat)]) = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end