theory Recon019
imports Main
begin

lemma ite__medium__1_zipperposition: "(if (n::nat) = n then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__1_e: "(if (n::nat) = n then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__1_vampire: "(if (n::nat) = n then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__1_spass: "(if (n::nat) = n then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__1_cvc5: "(if (n::nat) = n then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__2_zipperposition: "min (m::nat) a \<le> max m a"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__2_e: "min (m::nat) a \<le> max m a"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__2_vampire: "min (m::nat) a \<le> max m a"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__2_spass: "min (m::nat) a \<le> max m a"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__2_cvc5: "min (m::nat) a \<le> max m a"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_zipperposition: "(let x = (a::nat); y = u in x + y) = a + u"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_e: "(let x = (a::nat); y = u in x + y) = a + u"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_vampire: "(let x = (a::nat); y = u in x + y) = a + u"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_spass: "(let x = (a::nat); y = u in x + y) = a + u"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_cvc5: "(let x = (a::nat); y = u in x + y) = a + u"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__4_zipperposition: "distinct [(m::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__4_e: "distinct [(m::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__4_vampire: "distinct [(m::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__4_spass: "distinct [(m::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__simple__4_cvc5: "distinct [(m::nat)]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_zipperposition: "fst (z, n) = (z::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_e: "fst (z, n) = (z::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_vampire: "fst (z, n) = (z::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_spass: "fst (z, n) = (z::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_cvc5: "fst (z, n) = (z::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_zipperposition: "(\<lambda>x::nat. 0)((n::nat) := 1) n = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_e: "(\<lambda>x::nat. 0)((n::nat) := 1) n = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_vampire: "(\<lambda>x::nat. 0)((n::nat) := 1) n = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_spass: "(\<lambda>x::nat. 0)((n::nat) := 1) n = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__6_cvc5: "(\<lambda>x::nat. 0)((n::nat) := 1) n = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__7_zipperposition: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__7_e: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__7_vampire: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__7_spass: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__7_cvc5: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_zipperposition: "set [a] \<union> set [b] = set [a, (b::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_e: "set [a] \<union> set [b] = set [a, (b::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_vampire: "set [a] \<union> set [b] = set [a, (b::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_spass: "set [a] \<union> set [b] = set [a, (b::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_cvc5: "set [a] \<union> set [b] = set [a, (b::nat)]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_zipperposition: "(u::int) * (-1) = -u"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_e: "(u::int) * (-1) = -u"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_vampire: "(u::int) * (-1) = -u"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_spass: "(u::int) * (-1) = -u"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__9_cvc5: "(u::int) * (-1) = -u"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_zipperposition: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_e: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_vampire: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_spass: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__10_cvc5: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_zipperposition: "(5::nat) mod 2 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_e: "(5::nat) mod 2 = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_vampire: "(5::nat) mod 2 = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_spass: "(5::nat) mod 2 = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_cvc5: "(5::nat) mod 2 = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__12_zipperposition: "the (Some (y::nat)) = y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__12_e: "the (Some (y::nat)) = y"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__12_vampire: "the (Some (y::nat)) = y"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__12_spass: "the (Some (y::nat)) = y"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__12_cvc5: "the (Some (y::nat)) = y"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_zipperposition: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_e: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_vampire: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_spass: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__13_cvc5: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__14_zipperposition: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__14_e: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__14_vampire: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__14_spass: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__14_cvc5: "filter (\<lambda>x. True) [(1::nat)] = [1]"
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