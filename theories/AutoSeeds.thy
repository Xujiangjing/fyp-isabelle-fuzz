theory AutoSeeds
imports Main
begin

lemma seed_1: "fof = (fof::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_2: "fof + 0 = (fof::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_3: "fof * 1 = (fof::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_4: "tff = (tff::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_5: "tff + 0 = (tff::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_6: "tff * 1 = (tff::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_7: "cnf = (cnf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_8: "cnf + 0 = (cnf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_9: "cnf * 1 = (cnf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_10: "thf = (thf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_11: "thf + 0 = (thf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_12: "thf * 1 = (thf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_13: "tcf = (tcf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_14: "tcf + 0 = (tcf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_15: "tcf * 1 = (tcf::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_16: "include = (include::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_17: "include + 0 = (include::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_18: "include * 1 = (include::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_19: "type = (type::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_20: "type + 0 = (type::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_21: "type * 1 = (type::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_22: "axiom = (axiom::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_23: "axiom + 0 = (axiom::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_24: "axiom * 1 = (axiom::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_25: "lemma = (lemma::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_26: "lemma + 0 = (lemma::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_27: "lemma * 1 = (lemma::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_28: "theorem = (theorem::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_29: "theorem + 0 = (theorem::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_30: "theorem * 1 = (theorem::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_31: "(x::nat) ≤ x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_32: "(x::nat) < x + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_33: "(y::nat) ≤ y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_34: "(y::nat) < y + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_35: "(z::nat) ≤ z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_36: "(z::nat) < z + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_37: "(foo::nat) ≤ foo"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_38: "(foo::nat) < foo + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_39: "(bar::nat) ≤ bar"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma seed_40: "(bar::nat) < bar + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end