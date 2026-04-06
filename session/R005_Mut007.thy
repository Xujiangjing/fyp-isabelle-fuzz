theory R005_Mut007
imports Main
begin

lemma mut_1: "hd [d3] = (d3::int list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "(g9::bool) + q5 = q5 + g9"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "theorem = (theorem::string)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "(negated_conjecture::real) < negated_conjecture + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "set [(q0::real), plain] = {v, plain}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_6: "set [(s::string), type] = {v, type}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_7: "hd [tcf] = (tcf::real)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_8: "(o7::bool) + v6 = v6 + o7"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_9: "rev [(e5::char)] = [e5]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_10: "hd [b5] = (b5::string)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_11: "set [(r0::nat option), i0] = {v, i0}"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_12: "rev [(True::nat option)] = [True]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_13: "j9 + j9 = 2 * (j9::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_14: "p2 + 0 = (p2::real)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end