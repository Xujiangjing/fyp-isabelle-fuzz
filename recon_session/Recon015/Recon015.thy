theory Recon015
imports Main
begin

lemma sum__simple__1_zipperposition: "isl (Inl (w::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__1_e: "isl (Inl (w::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__1_vampire: "isl (Inl (w::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__1_spass: "isl (Inl (w::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__1_cvc5: "isl (Inl (w::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_zipperposition: "snd (v, y) = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_e: "snd (v, y) = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_vampire: "snd (v, y) = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_spass: "snd (v, y) = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_cvc5: "snd (v, y) = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__3_zipperposition: "concat [xs, ys] = xs @ (ys::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__3_e: "concat [xs, ys] = xs @ (ys::nat list)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__3_vampire: "concat [xs, ys] = xs @ (ys::nat list)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__3_spass: "concat [xs, ys] = xs @ (ys::nat list)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__3_cvc5: "concat [xs, ys] = xs @ (ys::nat list)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__4_zipperposition: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__4_e: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__4_vampire: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__4_spass: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__4_cvc5: "(\<lambda>x::nat. 0)((v::nat) := 1) v = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__5_zipperposition: "(v::int) + 0 = v"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__5_e: "(v::int) + 0 = v"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__5_vampire: "(v::int) + 0 = v"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__5_spass: "(v::int) + 0 = v"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__5_cvc5: "(v::int) + 0 = v"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_zipperposition: "(b::nat) ^ 1 = b"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_e: "(b::nat) ^ 1 = b"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_vampire: "(b::nat) ^ 1 = b"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_spass: "(b::nat) ^ 1 = b"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_cvc5: "(b::nat) ^ 1 = b"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__7_zipperposition: "max (y::nat) y = y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__7_e: "max (y::nat) y = y"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__7_vampire: "max (y::nat) y = y"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__7_spass: "max (y::nat) y = y"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__7_cvc5: "max (y::nat) y = y"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_zipperposition: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_e: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_vampire: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_spass: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__8_cvc5: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__9_zipperposition: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__9_e: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__9_vampire: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__9_spass: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__9_cvc5: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_zipperposition: "(if True then (u::nat) else v) = u"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_e: "(if True then (u::nat) else v) = u"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_vampire: "(if True then (u::nat) else v) = u"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_spass: "(if True then (u::nat) else v) = u"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_cvc5: "(if True then (u::nat) else v) = u"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__11_zipperposition: "Option.is_none (None :: nat option)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__11_e: "Option.is_none (None :: nat option)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__11_vampire: "Option.is_none (None :: nat option)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__11_spass: "Option.is_none (None :: nat option)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__11_cvc5: "Option.is_none (None :: nat option)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_zipperposition: "(\<lambda>x::nat. x + 1) z = z + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_e: "(\<lambda>x::nat. x + 1) z = z + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_vampire: "(\<lambda>x::nat. x + 1) z = z + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_spass: "(\<lambda>x::nat. x + 1) z = z + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_cvc5: "(\<lambda>x::nat. x + 1) z = z + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__13_zipperposition: "(y::nat) mod 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__13_e: "(y::nat) mod 1 = 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__13_vampire: "(y::nat) mod 1 = 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__13_spass: "(y::nat) mod 1 = 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__13_cvc5: "(y::nat) mod 1 = 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__14_zipperposition: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__14_e: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__14_vampire: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__14_spass: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__medium__14_cvc5: "(P \<longrightarrow> Q) \<longrightarrow> (\<not> Q \<longrightarrow> \<not> P)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__15_zipperposition: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__15_e: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__15_vampire: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__15_spass: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__15_cvc5: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end