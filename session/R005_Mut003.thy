theory R005_Mut003
imports Main
begin

lemma mut_1: "rev [(tcf::nat set)] = [tcf]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "length [(o::real)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "b5 = (b5::nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "sorted (sort [(s0::string), j7])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "(o1::int) * (tff1 + 1) = o1 * tff1 + o1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_6: "(t7::nat) < t7 + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_7: "(t6::int) + fof_x = fof_x + t6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_8: "rev [(a7::int list)] = [a7]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_9: "length [(f3::int list)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_10: "min (j8::bool) c <= max j8 c"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_11: "l0 + l0 = 2 * (l0::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_12: "set [(t9::nat list), u7] = {v, u7}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_13: "k1 + k1 = 2 * (k1::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_14: "hd [conjecture] = (conjecture::nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_15: "min (b3::int) o2 <= max b3 o2"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end