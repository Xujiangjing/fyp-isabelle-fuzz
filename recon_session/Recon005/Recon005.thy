theory Recon005
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

lemma set__medium__2_zipperposition: "set [u] \<union> set [m] = set [u, (m::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__2_e: "set [u] \<union> set [m] = set [u, (m::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__2_vampire: "set [u] \<union> set [m] = set [u, (m::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__2_spass: "set [u] \<union> set [m] = set [u, (m::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__2_cvc5: "set [u] \<union> set [m] = set [u, (m::nat)]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__3_zipperposition: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__3_e: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__3_vampire: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__3_spass: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__3_cvc5: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_zipperposition: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_e: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_vampire: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_spass: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__4_cvc5: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_zipperposition: "snd (x, w) = (w::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_e: "snd (x, w) = (w::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_vampire: "snd (x, w) = (w::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_spass: "snd (x, w) = (w::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__5_cvc5: "snd (x, w) = (w::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_zipperposition: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_e: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_vampire: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_spass: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__6_cvc5: "isl (Inl (a::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_zipperposition: "min (x::nat) w \<le> max x w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_e: "min (x::nat) w \<le> max x w"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_vampire: "min (x::nat) w \<le> max x w"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_spass: "min (x::nat) w \<le> max x w"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__7_cvc5: "min (x::nat) w \<le> max x w"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_zipperposition: "(let x = (y::nat) in x + 1) = y + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_e: "(let x = (y::nat) in x + 1) = y + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_vampire: "(let x = (y::nat) in x + 1) = y + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_spass: "(let x = (y::nat) in x + 1) = y + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__8_cvc5: "(let x = (y::nat) in x + 1) = y + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_zipperposition: "length (map f xs) = length (xs::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_e: "length (map f xs) = length (xs::nat list)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_vampire: "length (map f xs) = length (xs::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_spass: "length (map f xs) = length (xs::nat list)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_cvc5: "length (map f xs) = length (xs::nat list)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__10_zipperposition: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__10_e: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__10_vampire: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__10_spass: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__10_cvc5: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_zipperposition: "(y::nat) div 1 = y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_e: "(y::nat) div 1 = y"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_vampire: "(y::nat) div 1 = y"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_spass: "(y::nat) div 1 = y"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__11_cvc5: "(y::nat) div 1 = y"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__12_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__12_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__12_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__12_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__12_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__13_zipperposition: "(\<lambda>x::nat. x + 1) m = m + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__13_e: "(\<lambda>x::nat. x + 1) m = m + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__13_vampire: "(\<lambda>x::nat. x + 1) m = m + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__13_spass: "(\<lambda>x::nat. x + 1) m = m + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__13_cvc5: "(\<lambda>x::nat. x + 1) m = m + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_zipperposition: "(if (b::nat) = b then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_e: "(if (b::nat) = b then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_vampire: "(if (b::nat) = b then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_spass: "(if (b::nat) = b then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__14_cvc5: "(if (b::nat) = b then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__15_zipperposition: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__15_e: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__15_vampire: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__15_spass: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__15_cvc5: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end