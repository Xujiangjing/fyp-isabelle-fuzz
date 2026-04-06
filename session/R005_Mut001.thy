theory R005_Mut001
imports Main
begin

lemma mut_1: "set [(d3::int), m1] = {v, m1}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "(o0::nat option) < o0 + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "(b2::real) < b2 + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "rev [(s4::nat option)] = [s4]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "thf * 1 = (thf::int)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_6: "hd [r9] = (r9::real)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_7: "(p4::int list) + False = False + p4"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_8: "(o7::int list) + z7 = z7 + o7"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_9: "hd [e6] = (e6::int)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_10: "hd [v7] = (v7::real)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end