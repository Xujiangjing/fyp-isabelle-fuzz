theory FuzzTest014
imports Main
begin

lemma true_1: "hd [u] = (u::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_2: "set [x, n] = set [n, (x::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_3: "(u::nat) < u"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_4: "(w::nat) + 1 = w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_5: "length (xs @ ys) = length xs + length (ys::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_6: "(n::nat) < n + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end