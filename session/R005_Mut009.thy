theory R005_Mut009
imports Main
begin

lemma mut_1: "x8 * 1 = (x8::int)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "length [(fof::nat option)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "sorted (sort [(s8::string), cnf])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "length [(True::bool)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "t1 + 0 = (t1::int list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_6: "min (y9::int list) b0 <= max y9 b0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_7: "i5 + 0 = (i5::char)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_8: "(d2::nat list) * (fof_x + 1) = d2 * fof_x + d2"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_9: "sorted (sort [(m3::nat), p2])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_10: "True = (True::int list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_11: "set [(cnf_::int list), n5] = {v, n5}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_12: "sorted (sort [(p6::int), l0])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_13: "sorted (sort [(i::bool), m9])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end