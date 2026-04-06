theory FuzzTest015
imports Main
begin

lemma true_1: "(b::nat) * 1 = b"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_2: "Suc (n::nat) = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_3: "Suc (x::nat) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_4: "length [v] = (1::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_5: "(n::nat) * 1 = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_6: "\<exists>x::nat. x < 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_7: "(m::nat) * 1 = m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_8: "(a::nat) + m = m + a"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_9: "rev [(1::nat), 2] = [1, 2]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end