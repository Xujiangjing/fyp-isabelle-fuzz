theory Recon018
imports Main
begin

lemma logic__simple__1_zipperposition: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_e: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_vampire: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_spass: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_cvc5: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_zipperposition: "(n::nat) * 1 = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_e: "(n::nat) * 1 = n"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_vampire: "(n::nat) * 1 = n"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_spass: "(n::nat) * 1 = n"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__2_cvc5: "(n::nat) * 1 = n"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_zipperposition: "finite (set [m, (v::nat)])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_e: "finite (set [m, (v::nat)])"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_vampire: "finite (set [m, (v::nat)])"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_spass: "finite (set [m, (v::nat)])"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__3_cvc5: "finite (set [m, (v::nat)])"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__4_zipperposition: "(if True then (y::nat) else x) = y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__4_e: "(if True then (y::nat) else x) = y"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__4_vampire: "(if True then (y::nat) else x) = y"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__4_spass: "(if True then (y::nat) else x) = y"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__4_cvc5: "(if True then (y::nat) else x) = y"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__5_zipperposition: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__5_e: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__5_vampire: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__5_spass: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__5_cvc5: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_zipperposition: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_e: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_vampire: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_spass: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_cvc5: "\<not> Option.is_none (Some (z::nat))"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_zipperposition: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_e: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_vampire: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_spass: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_cvc5: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_zipperposition: "(let x = (b::nat); y = u in x + y) = b + u"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_e: "(let x = (b::nat); y = u in x + y) = b + u"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_vampire: "(let x = (b::nat); y = u in x + y) = b + u"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_spass: "(let x = (b::nat); y = u in x + y) = b + u"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_cvc5: "(let x = (b::nat); y = u in x + y) = b + u"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_zipperposition: "(m::int) + u = u + m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_e: "(m::int) + u = u + m"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_vampire: "(m::int) + u = u + m"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_spass: "(m::int) + u = u + m"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_cvc5: "(m::int) + u = u + m"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__10_zipperposition: "(x::nat) div 1 = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__10_e: "(x::nat) div 1 = x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__10_vampire: "(x::nat) div 1 = x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__10_spass: "(x::nat) div 1 = x"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__10_cvc5: "(x::nat) div 1 = x"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__11_zipperposition: "sorted [(1::nat), 2, 3]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__11_e: "sorted [(1::nat), 2, 3]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__11_vampire: "sorted [(1::nat), 2, 3]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__11_spass: "sorted [(1::nat), 2, 3]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__11_cvc5: "sorted [(1::nat), 2, 3]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__12_zipperposition: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__12_e: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__12_vampire: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__12_spass: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__12_cvc5: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_zipperposition: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_e: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_vampire: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_spass: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_cvc5: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_zipperposition: "\<not> isl (Inr (n::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_e: "\<not> isl (Inr (n::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_vampire: "\<not> isl (Inr (n::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_spass: "\<not> isl (Inr (n::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__14_cvc5: "\<not> isl (Inr (n::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__15_zipperposition: "fst (n, y) = (n::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__15_e: "fst (n, y) = (n::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__15_vampire: "fst (n, y) = (n::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__15_spass: "fst (n, y) = (n::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__15_cvc5: "fst (n, y) = (n::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end