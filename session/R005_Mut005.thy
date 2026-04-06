theory R005_Mut005
imports Main
begin

lemma mut_1: "s3 + s3 = 2 * (s3::nat set)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "v8 * 1 = (v8::char)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "o1 = (o1::int)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "length [(p::real)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "x_y_z + x_y_z = 2 * (x_y_z::char)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_6: "rev [(i6::nat option)] = [i6]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_7: "set [(o::string), k2] = {v, k2}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_8: "length [(type::bool)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_9: "(o6::nat option) + m6 = m6 + o6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_10: "min (b1::char) tff1 <= max b1 tff1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_11: "rev [(m7::bool)] = [m7]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_12: "negated_conjecture + 0 = (negated_conjecture::nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_13: "length [(d8::nat list)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_14: "sorted (sort [(cnf::string), y7])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_15: "(e0::real) < e0 + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end