theory FuzzTest005
imports Main
begin

lemma false_1: "(0::nat) = Suc 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_2: "0 + (n::nat) = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_3: "(0::nat) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_4: "(n::nat) = n \<or> False"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_5: "hd [v] = (v::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma false_6: "length ([(1::nat)]) = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma true_7: "(v::nat) + x = x + v"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end