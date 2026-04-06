theory TypeStress
imports Main
begin

lemma type_nat_1: "(x::nat) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_int_2: "(x::int) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_bool_3: "(x::bool) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_real_4: "(x::real) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_list_5: "(x::nat list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_list_int_6: "(x::int list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_list_bool_7: "(x::bool list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_set_nat_8: "(x::nat set) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_option_nat_9: "(x::nat option) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_list_list_10: "(x::nat list list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_option_list_11: "(x::nat option list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_list_option_12: "(x::nat list option) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_poly_a_17: "(x::'a) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma type_poly_list_18: "(x::'a list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma fun_app_21: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma fun_curried_22: "(\<lambda>x::nat. \<lambda>y::nat. x + y) a b = a + (b::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma prod_23: "fst (a, b) = (a::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

end