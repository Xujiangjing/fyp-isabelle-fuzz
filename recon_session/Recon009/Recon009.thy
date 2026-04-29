theory Recon009
imports Main
begin

lemma int_arith__medium__1_zipperposition: "(x::int) * (-1) = -x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_e: "(x::int) * (-1) = -x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_vampire: "(x::int) * (-1) = -x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_spass: "(x::int) * (-1) = -x"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_cvc5: "(x::int) * (-1) = -x"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__2_zipperposition: "(if (u::nat) = u then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__2_e: "(if (u::nat) = u then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__2_vampire: "(if (u::nat) = u then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__2_spass: "(if (u::nat) = u then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__2_cvc5: "(if (u::nat) = u then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_zipperposition: "y = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_e: "y = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_vampire: "y = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_spass: "y = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_cvc5: "y = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_zipperposition: "Option.is_none (None :: nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_e: "Option.is_none (None :: nat option)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_vampire: "Option.is_none (None :: nat option)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_spass: "Option.is_none (None :: nat option)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_cvc5: "Option.is_none (None :: nat option)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__5_zipperposition: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__5_e: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__5_vampire: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__5_spass: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__5_cvc5: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_zipperposition: "(\<lambda>x::nat. 0)((a::nat) := 1) a = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_e: "(\<lambda>x::nat. 0)((a::nat) := 1) a = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_vampire: "(\<lambda>x::nat. 0)((a::nat) := 1) a = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_spass: "(\<lambda>x::nat. 0)((a::nat) := 1) a = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_cvc5: "(\<lambda>x::nat. 0)((a::nat) := 1) a = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__7_zipperposition: "(0::nat) div 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__7_e: "(0::nat) div 1 = 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__7_vampire: "(0::nat) div 1 = 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__7_spass: "(0::nat) div 1 = 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__7_cvc5: "(0::nat) div 1 = 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__8_zipperposition: "snd (m, z) = (z::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__8_e: "snd (m, z) = (z::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__8_vampire: "snd (m, z) = (z::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__8_spass: "snd (m, z) = (z::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__8_cvc5: "snd (m, z) = (z::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__9_zipperposition: "(y::nat) \<le> y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__9_e: "(y::nat) \<le> y"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__9_vampire: "(y::nat) \<le> y"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__9_spass: "(y::nat) \<le> y"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__9_cvc5: "(y::nat) \<le> y"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_zipperposition: "(m::nat) = m \<or> False"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_e: "(m::nat) = m \<or> False"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_vampire: "(m::nat) = m \<or> False"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_spass: "(m::nat) = m \<or> False"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_cvc5: "(m::nat) = m \<or> False"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__12_zipperposition: "(let x = (z::nat); y = y in x + y) = z + y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__12_e: "(let x = (z::nat); y = y in x + y) = z + y"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__12_vampire: "(let x = (z::nat); y = y in x + y) = z + y"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__12_spass: "(let x = (z::nat); y = y in x + y) = z + y"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__12_cvc5: "(let x = (z::nat); y = y in x + y) = z + y"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__13_zipperposition: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__13_e: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__13_vampire: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__13_spass: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__13_cvc5: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_zipperposition: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_e: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_vampire: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_spass: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_cvc5: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__15_zipperposition: "distinct [(u::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__15_e: "distinct [(u::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__15_vampire: "distinct [(u::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__15_spass: "distinct [(u::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__15_cvc5: "distinct [(u::nat)]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end