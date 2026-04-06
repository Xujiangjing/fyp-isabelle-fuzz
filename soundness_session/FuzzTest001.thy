theory FuzzTest001
imports Main
begin

lemma true_1: "hd [m] = (m::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_2: "length (xs @ ys) = length xs + length (ys::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_3: "\<forall>x::nat. x = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma keyword_include_4: "include = (include :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_5: "True \<longrightarrow> (m::nat) = m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_6: "rev [(1::nat), 2] = [1, 2]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end