theory Recon017
imports Main
begin

lemma int_arith__medium__1_zipperposition: "(y::int) + z = z + y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_e: "(y::int) + z = z + y"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_vampire: "(y::int) + z = z + y"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_spass: "(y::int) + z = z + y"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_cvc5: "(y::int) + z = z + y"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_zipperposition: "Suc (z::nat) = z + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_e: "Suc (z::nat) = z + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_vampire: "Suc (z::nat) = z + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_spass: "Suc (z::nat) = z + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_cvc5: "Suc (z::nat) = z + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_zipperposition: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_e: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_vampire: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_spass: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_cvc5: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__4_zipperposition: "y = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__4_e: "y = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__4_vampire: "y = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__4_spass: "y = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__4_cvc5: "y = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__5_zipperposition: "tl [u] = ([]::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__5_e: "tl [u] = ([]::nat list)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__5_vampire: "tl [u] = ([]::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__5_spass: "tl [u] = ([]::nat list)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__5_cvc5: "tl [u] = ([]::nat list)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__6_zipperposition: "(\<exists>x::nat. x = 0)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__6_e: "(\<exists>x::nat. x = 0)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__6_vampire: "(\<exists>x::nat. x = 0)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__6_spass: "(\<exists>x::nat. x = 0)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__6_cvc5: "(\<exists>x::nat. x = 0)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_zipperposition: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_e: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_vampire: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_spass: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_cvc5: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__8_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__8_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__8_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__8_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__8_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_zipperposition: "snd (z, y) = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_e: "snd (z, y) = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_vampire: "snd (z, y) = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_spass: "snd (z, y) = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_cvc5: "snd (z, y) = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_zipperposition: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_e: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_vampire: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_spass: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_cvc5: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_zipperposition: "(m::nat) div 1 = m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_e: "(m::nat) div 1 = m"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_vampire: "(m::nat) div 1 = m"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_spass: "(m::nat) div 1 = m"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_cvc5: "(m::nat) div 1 = m"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_zipperposition: "(\<lambda>x::nat. x) m = m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_e: "(\<lambda>x::nat. x) m = m"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_vampire: "(\<lambda>x::nat. x) m = m"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_spass: "(\<lambda>x::nat. x) m = m"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_cvc5: "(\<lambda>x::nat. x) m = m"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__13_zipperposition: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__13_e: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__13_vampire: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__13_spass: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__13_cvc5: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__14_zipperposition: "(n::nat) ^ 1 = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__14_e: "(n::nat) ^ 1 = n"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__14_vampire: "(n::nat) ^ 1 = n"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__14_spass: "(n::nat) ^ 1 = n"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__14_cvc5: "(n::nat) ^ 1 = n"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_zipperposition: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_e: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_vampire: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_spass: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_cvc5: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end