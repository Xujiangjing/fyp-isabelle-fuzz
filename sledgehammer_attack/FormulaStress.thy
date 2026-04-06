theory FormulaStress
imports Main
begin

lemma formula_deep_add_1: "(((((z::nat) + 0) + 0) + 0) + 0) = z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_nested_ite_2: "(if True then (if False then 0 else (n::nat)) else 0) = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_let_bind_3: "(let x = (z::nat) in x + 0) = z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_multi_let_4: "(let x = (y::nat); y = x in y) = y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_lambda_app_5: "(\<lambda>x::nat. x) z = (z::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_nested_lambda_6: "(\<lambda>x::nat. (\<lambda>y::nat. x + y)) z m = z + (m::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_case_nat_7: "(case (y::nat) of 0 \<Rightarrow> 1 | Suc n \<Rightarrow> n + 2) \<ge> (1::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_exists_witness_8: "\<exists>x::nat. x = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_forall_plus_zero_9: "\<forall>x::nat. x + 0 = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_nested_quant_10: "\<forall>x::nat. \<exists>y::nat. y = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_eq_chain_11: "(b::nat) = b \<and> a = (a::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_bool_eq_12: "((b::nat) = a) = ((a::nat) = b)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_unit_eq_13: "() = ()"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_large_numeral_14: "(2147483647::nat) + 1 = 2147483648"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_neg_int_15: "(- (1::int)) + 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_div_nat_16: "(6::nat) div 2 = 3"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

lemma formula_mod_nat_17: "(7::nat) mod 3 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 15, overlord]
  oops

end