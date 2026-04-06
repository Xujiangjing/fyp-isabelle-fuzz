theory R005_Mut000
imports Main
begin

lemma mut_1: "sorted (sort [(u8::int list), d9])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "sorted (sort [(m2::nat option), e8])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "(r8::nat set) + c0 = c0 + r8"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "rev [(q3::real)] = [q3]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "(axiom::bool) + i = i + axiom"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_6: "hd [e8] = (e8::nat set)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_7: "length [(u9::nat option)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_8: "min (y1::char) s7 <= max y1 s7"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_9: "set [(j8::string), p6] = {v, p6}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_10: "r0 * 1 = (r0::string)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_11: "sorted (sort [(s::nat option), e4])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_12: "(lemma::nat list) < lemma + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_13: "o6 = (o6::int)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end