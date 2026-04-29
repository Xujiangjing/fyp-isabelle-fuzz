theory Recon014
imports Main
begin

lemma divmod__medium__1_zipperposition: "(m::nat) div 1 = m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__1_e: "(m::nat) div 1 = m"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__1_vampire: "(m::nat) div 1 = m"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__1_spass: "(m::nat) div 1 = m"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__1_cvc5: "(m::nat) div 1 = m"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__2_zipperposition: "Option.is_none (None :: nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__2_e: "Option.is_none (None :: nat option)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__2_vampire: "Option.is_none (None :: nat option)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__2_spass: "Option.is_none (None :: nat option)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__2_cvc5: "Option.is_none (None :: nat option)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_zipperposition: "(let x = (a::nat); y = w in x + y) = a + w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_e: "(let x = (a::nat); y = w in x + y) = a + w"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_vampire: "(let x = (a::nat); y = w in x + y) = a + w"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_spass: "(let x = (a::nat); y = w in x + y) = a + w"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_cvc5: "(let x = (a::nat); y = w in x + y) = a + w"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__4_zipperposition: "set [b, a] = set [a, (b::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__4_e: "set [b, a] = set [a, (b::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__4_vampire: "set [b, a] = set [a, (b::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__4_spass: "set [b, a] = set [a, (b::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__4_cvc5: "set [b, a] = set [a, (b::nat)]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_zipperposition: "y + 0 = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_e: "y + 0 = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_vampire: "y + 0 = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_spass: "y + 0 = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_cvc5: "y + 0 = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__6_zipperposition: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__6_e: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__6_vampire: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__6_spass: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__6_cvc5: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_zipperposition: "fst (z, n) = (z::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_e: "fst (z, n) = (z::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_vampire: "fst (z, n) = (z::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_spass: "fst (z, n) = (z::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__7_cvc5: "fst (z, n) = (z::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_zipperposition: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_e: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_vampire: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_spass: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_cvc5: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_zipperposition: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_e: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_vampire: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_spass: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__9_cvc5: "(if (v::nat) = v then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__10_zipperposition: "(\<lambda>x::nat. x + 1) n = n + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__10_e: "(\<lambda>x::nat. x + 1) n = n + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__10_vampire: "(\<lambda>x::nat. x + 1) n = n + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__10_spass: "(\<lambda>x::nat. x + 1) n = n + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__10_cvc5: "(\<lambda>x::nat. x + 1) n = n + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__11_zipperposition: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__11_e: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__11_vampire: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__11_spass: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__11_cvc5: "(P \<or> Q) = (Q \<or> P)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__12_zipperposition: "\<bar>(w::int)\<bar> \<ge> 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__12_e: "\<bar>(w::int)\<bar> \<ge> 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__12_vampire: "\<bar>(w::int)\<bar> \<ge> 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__12_spass: "\<bar>(w::int)\<bar> \<ge> 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__12_cvc5: "\<bar>(w::int)\<bar> \<ge> 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_zipperposition: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_e: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_vampire: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_spass: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__13_cvc5: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__14_zipperposition: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__14_e: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__14_vampire: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__14_spass: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__14_cvc5: "set (xs @ ys) = set xs \<union> set (ys::nat list)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_zipperposition: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_e: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_vampire: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_spass: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_cvc5: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end