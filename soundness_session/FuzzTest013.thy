theory FuzzTest013
imports Main
begin

lemma true_1: "length (xs @ ys) = length xs + length (ys::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_2: "length ([(1::nat)]) = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_3: "(0::nat) = Suc 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_4: "(a::nat) \<in> set [a, x]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_5: "(w::nat) \<le> w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_6: "\<forall>x::nat. x = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_7: "length ([(1::nat)]) = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_8: "(a::nat) \<le> a"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end