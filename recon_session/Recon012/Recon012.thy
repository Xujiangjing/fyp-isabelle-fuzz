theory Recon012
imports Main
begin

lemma power__simple__1_zipperposition: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__1_e: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__1_vampire: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__1_spass: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__1_cvc5: "(2::nat) ^ 0 = 1"
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

lemma int_arith__medium__3_zipperposition: "\<bar>(m::int)\<bar> \<ge> 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__3_e: "\<bar>(m::int)\<bar> \<ge> 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__3_vampire: "\<bar>(m::int)\<bar> \<ge> 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__3_spass: "\<bar>(m::int)\<bar> \<ge> 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__3_cvc5: "\<bar>(m::int)\<bar> \<ge> 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_zipperposition: "map (\<lambda>x. x + 1) [(u::nat)] = [u + 1]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_e: "map (\<lambda>x. x + 1) [(u::nat)] = [u + 1]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_vampire: "map (\<lambda>x. x + 1) [(u::nat)] = [u + 1]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_spass: "map (\<lambda>x. x + 1) [(u::nat)] = [u + 1]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__4_cvc5: "map (\<lambda>x. x + 1) [(u::nat)] = [u + 1]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_zipperposition: "Suc (w::nat) = w + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_e: "Suc (w::nat) = w + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_vampire: "Suc (w::nat) = w + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_spass: "Suc (w::nat) = w + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__5_cvc5: "Suc (w::nat) = w + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_zipperposition: "the (Some (n::nat)) = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_e: "the (Some (n::nat)) = n"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_vampire: "the (Some (n::nat)) = n"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_spass: "the (Some (n::nat)) = n"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__6_cvc5: "the (Some (n::nat)) = n"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__7_zipperposition: "(v::nat) \<in> set [v, u]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__7_e: "(v::nat) \<in> set [v, u]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__7_vampire: "(v::nat) \<in> set [v, u]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__7_spass: "(v::nat) \<in> set [v, u]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__7_cvc5: "(v::nat) \<in> set [v, u]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_zipperposition: "\<not> isl (Inr (u::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_e: "\<not> isl (Inr (u::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_vampire: "\<not> isl (Inr (u::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_spass: "\<not> isl (Inr (u::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_cvc5: "\<not> isl (Inr (u::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_zipperposition: "snd (z, x) = (x::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_e: "snd (z, x) = (x::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_vampire: "snd (z, x) = (x::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_spass: "snd (z, x) = (x::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__9_cvc5: "snd (z, x) = (x::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__10_zipperposition: "rev (xs @ ys) = rev ys @ rev (xs::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__10_e: "rev (xs @ ys) = rev ys @ rev (xs::nat list)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__10_vampire: "rev (xs @ ys) = rev ys @ rev (xs::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__10_spass: "rev (xs @ ys) = rev ys @ rev (xs::nat list)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__hard__10_cvc5: "rev (xs @ ys) = rev ys @ rev (xs::nat list)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__11_zipperposition: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__11_e: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__11_vampire: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__11_spass: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__11_cvc5: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__12_zipperposition: "(if True then (n::nat) else b) = n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__12_e: "(if True then (n::nat) else b) = n"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__12_vampire: "(if True then (n::nat) else b) = n"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__12_spass: "(if True then (n::nat) else b) = n"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__12_cvc5: "(if True then (n::nat) else b) = n"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__13_zipperposition: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__13_e: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__13_vampire: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__13_spass: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__13_cvc5: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__14_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__14_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__14_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__14_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__14_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_zipperposition: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_e: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_vampire: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_spass: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_cvc5: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end