theory FuzzTest009
imports Main
begin

lemma true_1: "set [b, y] = set [y, (b::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_2: "(n::nat) < n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_3: "set [y, b] = set [b, (y::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_4: "Suc (v::nat) = v"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma keyword_tcf_5: "tcf = (tcf :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_6: "(m::nat) < m + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_7: "rev (rev xs) = (xs::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_8: "True = False"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_9: "(y::nat) < y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_10: "(y::nat) \<in> set [y, v]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end