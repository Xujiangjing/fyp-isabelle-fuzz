theory Recon007
imports Main
begin

lemma logic__simple__1_zipperposition: "(w::nat) = w \<or> False"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_e: "(w::nat) = w \<or> False"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_vampire: "(w::nat) = w \<or> False"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_spass: "(w::nat) = w \<or> False"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_cvc5: "(w::nat) = w \<or> False"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_zipperposition: "fst (x, w) = (x::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_e: "fst (x, w) = (x::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_vampire: "fst (x, w) = (x::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_spass: "fst (x, w) = (x::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_cvc5: "fst (x, w) = (x::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_zipperposition: "max (z::nat) z = z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_e: "max (z::nat) z = z"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_vampire: "max (z::nat) z = z"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_spass: "max (z::nat) z = z"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_cvc5: "max (z::nat) z = z"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_zipperposition: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_e: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_vampire: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_spass: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_cvc5: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__5_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__5_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__5_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__5_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__5_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_zipperposition: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_e: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_vampire: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_spass: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_cvc5: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_zipperposition: "Option.is_none (None :: nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_e: "Option.is_none (None :: nat option)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_vampire: "Option.is_none (None :: nat option)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_spass: "Option.is_none (None :: nat option)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__7_cvc5: "Option.is_none (None :: nat option)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__8_zipperposition: "(x::nat) \<in> set [x, a]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__8_e: "(x::nat) \<in> set [x, a]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__8_vampire: "(x::nat) \<in> set [x, a]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__8_spass: "(x::nat) \<in> set [x, a]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__8_cvc5: "(x::nat) \<in> set [x, a]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__9_zipperposition: "(let x = (m::nat); y = x in x + y) = m + x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__9_e: "(let x = (m::nat); y = x in x + y) = m + x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__9_vampire: "(let x = (m::nat); y = x in x + y) = m + x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__9_spass: "(let x = (m::nat); y = x in x + y) = m + x"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__9_cvc5: "(let x = (m::nat); y = x in x + y) = m + x"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__10_zipperposition: "(u::int) + b = b + u"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__10_e: "(u::int) + b = b + u"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__10_vampire: "(u::int) + b = b + u"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__10_spass: "(u::int) + b = b + u"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__10_cvc5: "(u::int) + b = b + u"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__11_zipperposition: "(\<lambda>x::nat. 0)((w::nat) := 1) w = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__11_e: "(\<lambda>x::nat. 0)((w::nat) := 1) w = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__11_vampire: "(\<lambda>x::nat. 0)((w::nat) := 1) w = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__11_spass: "(\<lambda>x::nat. 0)((w::nat) := 1) w = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__11_cvc5: "(\<lambda>x::nat. 0)((w::nat) := 1) w = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__12_zipperposition: "(4::nat) div 2 = 2"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__12_e: "(4::nat) div 2 = 2"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__12_vampire: "(4::nat) div 2 = 2"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__12_spass: "(4::nat) div 2 = 2"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__12_cvc5: "(4::nat) div 2 = 2"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__13_zipperposition: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__13_e: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__13_vampire: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__13_spass: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__13_cvc5: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_zipperposition: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_e: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_vampire: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_spass: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_cvc5: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__15_zipperposition: "(1::nat) ^ u = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__15_e: "(1::nat) ^ u = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__15_vampire: "(1::nat) ^ u = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__15_spass: "(1::nat) ^ u = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__15_cvc5: "(1::nat) ^ u = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end