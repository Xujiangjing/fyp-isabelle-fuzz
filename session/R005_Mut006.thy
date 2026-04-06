theory R005_Mut006
imports Main
begin

lemma mut_1: "True + 0 = (True::string)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "x1 + 0 = (x1::real)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "v9 + v9 = 2 * (v9::int)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "rev [(h7::nat option)] = [h7]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "d0 + d0 = 2 * (d0::nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_6: "rev [(q7::nat)] = [q7]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_7: "set [(z1::int), w2] = {v, w2}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_8: "set [(c5::int list), h6] = {v, h6}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_9: "rev [(i3::bool)] = [i3]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_10: "m8 + 0 = (m8::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_11: "length [(hypothesis::nat option)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_12: "min (g2::int list) c <= max g2 c"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_13: "n3 = (n3::nat set)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end