theory Recon002
imports Main
begin

lemma hof__simple__1_zipperposition: "(\<lambda>x::nat. x + 1) a = a + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__1_e: "(\<lambda>x::nat. x + 1) a = a + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__1_vampire: "(\<lambda>x::nat. x + 1) a = a + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__1_spass: "(\<lambda>x::nat. x + 1) a = a + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__1_cvc5: "(\<lambda>x::nat. x + 1) a = a + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__2_zipperposition: "nth [w, b] 0 = (w::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__2_e: "nth [w, b] 0 = (w::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__2_vampire: "nth [w, b] 0 = (w::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__2_spass: "nth [w, b] 0 = (w::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__2_cvc5: "nth [w, b] 0 = (w::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_zipperposition: "(let x = (x::nat) in x + 1) = x + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_e: "(let x = (x::nat) in x + 1) = x + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_vampire: "(let x = (x::nat) in x + 1) = x + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_spass: "(let x = (x::nat) in x + 1) = x + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_cvc5: "(let x = (x::nat) in x + 1) = x + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_zipperposition: "the (Some (w::nat)) = w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_e: "the (Some (w::nat)) = w"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_vampire: "the (Some (w::nat)) = w"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_spass: "the (Some (w::nat)) = w"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_cvc5: "the (Some (w::nat)) = w"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__5_zipperposition: "(x::int) * (-1) = -x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__5_e: "(x::int) * (-1) = -x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__5_vampire: "(x::int) * (-1) = -x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__5_spass: "(x::int) * (-1) = -x"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__5_cvc5: "(x::int) * (-1) = -x"
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

lemma pair__simple__7_zipperposition: "snd (z, y) = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_e: "snd (z, y) = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_vampire: "snd (z, y) = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_spass: "snd (z, y) = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_cvc5: "snd (z, y) = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__8_zipperposition: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__8_e: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__8_vampire: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__8_spass: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__8_cvc5: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_zipperposition: "(if (m::nat) = m then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_e: "(if (m::nat) = m then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_vampire: "(if (m::nat) = m then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_spass: "(if (m::nat) = m then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_cvc5: "(if (m::nat) = m then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__10_zipperposition: "set [w, n] = set [n, (w::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__10_e: "set [w, n] = set [n, (w::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__10_vampire: "set [w, n] = set [n, (w::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__10_spass: "set [w, n] = set [n, (w::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__10_cvc5: "set [w, n] = set [n, (w::nat)]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__11_zipperposition: "max (w::nat) w = w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__11_e: "max (w::nat) w = w"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__11_vampire: "max (w::nat) w = w"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__11_spass: "max (w::nat) w = w"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__11_cvc5: "max (w::nat) w = w"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__12_zipperposition: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__12_e: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__12_vampire: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__12_spass: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__12_cvc5: "\<not> isl (Inr (x::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_zipperposition: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_e: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_vampire: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_spass: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_cvc5: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__14_zipperposition: "(4::nat) div 2 = 2"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__14_e: "(4::nat) div 2 = 2"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__14_vampire: "(4::nat) div 2 = 2"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__14_spass: "(4::nat) div 2 = 2"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__14_cvc5: "(4::nat) div 2 = 2"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end