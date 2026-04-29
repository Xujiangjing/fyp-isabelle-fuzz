theory Recon013
imports Main
begin

lemma let__medium__1_zipperposition: "(let x = (z::nat); y = m in x + y) = z + m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__1_e: "(let x = (z::nat); y = m in x + y) = z + m"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__1_vampire: "(let x = (z::nat); y = m in x + y) = z + m"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__1_spass: "(let x = (z::nat); y = m in x + y) = z + m"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__1_cvc5: "(let x = (z::nat); y = m in x + y) = z + m"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__2_zipperposition: "(0::nat) div 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__2_e: "(0::nat) div 1 = 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__2_vampire: "(0::nat) div 1 = 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__2_spass: "(0::nat) div 1 = 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__simple__2_cvc5: "(0::nat) div 1 = 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__3_zipperposition: "(\<lambda>x::nat. x + 1) u = u + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__3_e: "(\<lambda>x::nat. x + 1) u = u + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__3_vampire: "(\<lambda>x::nat. x + 1) u = u + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__3_spass: "(\<lambda>x::nat. x + 1) u = u + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__3_cvc5: "(\<lambda>x::nat. x + 1) u = u + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__4_zipperposition: "(w::nat) ^ 1 = w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__4_e: "(w::nat) ^ 1 = w"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__4_vampire: "(w::nat) ^ 1 = w"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__4_spass: "(w::nat) ^ 1 = w"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__4_cvc5: "(w::nat) ^ 1 = w"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__5_zipperposition: "last [n, a] = (a::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__5_e: "last [n, a] = (a::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__5_vampire: "last [n, a] = (a::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__5_spass: "last [n, a] = (a::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__5_cvc5: "last [n, a] = (a::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_zipperposition: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_e: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_vampire: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_spass: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_cvc5: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_zipperposition: "(w::nat) + Suc z = Suc (w + z)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_e: "(w::nat) + Suc z = Suc (w + z)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_vampire: "(w::nat) + Suc z = Suc (w + z)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_spass: "(w::nat) + Suc z = Suc (w + z)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_cvc5: "(w::nat) + Suc z = Suc (w + z)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__8_zipperposition: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__8_e: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__8_vampire: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__8_spass: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__8_cvc5: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_zipperposition: "Option.is_none (None :: nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_e: "Option.is_none (None :: nat option)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_vampire: "Option.is_none (None :: nat option)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_spass: "Option.is_none (None :: nat option)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_cvc5: "Option.is_none (None :: nat option)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__10_zipperposition: "(n::int) + 0 = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__10_e: "(n::int) + 0 = n"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__10_vampire: "(n::int) + 0 = n"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__10_spass: "(n::int) + 0 = n"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__10_cvc5: "(n::int) + 0 = n"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__11_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__11_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__11_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__11_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__11_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__12_zipperposition: "True \<and> True"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__12_e: "True \<and> True"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__12_vampire: "True \<and> True"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__12_spass: "True \<and> True"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__12_cvc5: "True \<and> True"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_zipperposition: "snd (x, m) = (m::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_e: "snd (x, m) = (m::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_vampire: "snd (x, m) = (m::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_spass: "snd (x, m) = (m::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_cvc5: "snd (x, m) = (m::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__14_zipperposition: "(n::nat) \<in> set [n, a]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__14_e: "(n::nat) \<in> set [n, a]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__14_vampire: "(n::nat) \<in> set [n, a]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__14_spass: "(n::nat) \<in> set [n, a]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__14_cvc5: "(n::nat) \<in> set [n, a]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__15_zipperposition: "(if True then (m::nat) else u) = m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__15_e: "(if True then (m::nat) else u) = m"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__15_vampire: "(if True then (m::nat) else u) = m"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__15_spass: "(if True then (m::nat) else u) = m"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__15_cvc5: "(if True then (m::nat) else u) = m"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end