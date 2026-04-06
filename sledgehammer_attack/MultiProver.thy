theory MultiProver
imports Main
begin

lemma mp_zipperposition_1: "(x::nat) + 0 = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma mp_e_2: "(x::nat) + 0 = x"
  sledgehammer [prover = e, slices = 1, timeout = 15, overlord]
  oops

lemma mp_vampire_3: "(x::nat) + 0 = x"
  sledgehammer [prover = vampire, slices = 1, timeout = 15, overlord]
  oops

lemma mp_zipperposition_4: "(x::nat) + y = y + x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma mp_e_5: "(x::nat) + y = y + x"
  sledgehammer [prover = e, slices = 1, timeout = 15, overlord]
  oops

lemma mp_vampire_6: "(x::nat) + y = y + x"
  sledgehammer [prover = vampire, slices = 1, timeout = 15, overlord]
  oops

lemma mp_zipperposition_7: "length [(x::nat)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma mp_e_8: "length [(x::nat)] = 1"
  sledgehammer [prover = e, slices = 1, timeout = 15, overlord]
  oops

lemma mp_vampire_9: "length [(x::nat)] = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 15, overlord]
  oops

lemma mp_zipperposition_10: "\<forall>x::nat. x + 0 = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma mp_e_11: "\<forall>x::nat. x + 0 = x"
  sledgehammer [prover = e, slices = 1, timeout = 15, overlord]
  oops

lemma mp_vampire_12: "\<forall>x::nat. x + 0 = x"
  sledgehammer [prover = vampire, slices = 1, timeout = 15, overlord]
  oops

lemma mp_zipperposition_13: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma mp_e_14: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 15, overlord]
  oops

lemma mp_vampire_15: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 15, overlord]
  oops

end