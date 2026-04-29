theory Recon010
imports Main
begin

lemma option__simple__1_zipperposition: "the (Some (w::nat)) = w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_e: "the (Some (w::nat)) = w"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_vampire: "the (Some (w::nat)) = w"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_spass: "the (Some (w::nat)) = w"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_cvc5: "the (Some (w::nat)) = w"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__2_zipperposition: "(v::nat) mod 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__2_e: "(v::nat) mod 1 = 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__2_vampire: "(v::nat) mod 1 = 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__2_spass: "(v::nat) mod 1 = 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__2_cvc5: "(v::nat) mod 1 = 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__3_zipperposition: "(1::nat) ^ b = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__3_e: "(1::nat) ^ b = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__3_vampire: "(1::nat) ^ b = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__3_spass: "(1::nat) ^ b = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__3_cvc5: "(1::nat) ^ b = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__4_zipperposition: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__4_e: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__4_vampire: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__4_spass: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__4_cvc5: "True \<longrightarrow> (v::nat) = v"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__5_zipperposition: "\<not> isl (Inr (z::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__5_e: "\<not> isl (Inr (z::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__5_vampire: "\<not> isl (Inr (z::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__5_spass: "\<not> isl (Inr (z::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__5_cvc5: "\<not> isl (Inr (z::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__6_zipperposition: "fst (b, v) = (b::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__6_e: "fst (b, v) = (b::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__6_vampire: "fst (b, v) = (b::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__6_spass: "fst (b, v) = (b::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__6_cvc5: "fst (b, v) = (b::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__7_zipperposition: "(if False then (u::nat) else a) = a"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__7_e: "(if False then (u::nat) else a) = a"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__7_vampire: "(if False then (u::nat) else a) = a"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__7_spass: "(if False then (u::nat) else a) = a"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__7_cvc5: "(if False then (u::nat) else a) = a"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__8_zipperposition: "(w::nat) < w + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__8_e: "(w::nat) < w + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__8_vampire: "(w::nat) < w + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__8_spass: "(w::nat) < w + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__8_cvc5: "(w::nat) < w + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_zipperposition: "nth [u, n] 0 = (u::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_e: "nth [u, n] 0 = (u::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_vampire: "nth [u, n] 0 = (u::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_spass: "nth [u, n] 0 = (u::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__9_cvc5: "nth [u, n] 0 = (u::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__10_zipperposition: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__10_e: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__10_vampire: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__10_spass: "(let x = (n::nat) in x + 1) = n + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__10_cvc5: "(let x = (n::nat) in x + 1) = n + 1"
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

lemma int_arith__simple__12_zipperposition: "(b::int) + 0 = b"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__12_e: "(b::int) + 0 = b"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__12_vampire: "(b::int) + 0 = b"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__12_spass: "(b::int) + 0 = b"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__12_cvc5: "(b::int) + 0 = b"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__13_zipperposition: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__13_e: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__13_vampire: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__13_spass: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__13_cvc5: "card (set [(y::nat)]) \<le> 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__14_zipperposition: "(\<lambda>x::nat. x) x = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__14_e: "(\<lambda>x::nat. x) x = x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__14_vampire: "(\<lambda>x::nat. x) x = x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__14_spass: "(\<lambda>x::nat. x) x = x"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__14_cvc5: "(\<lambda>x::nat. x) x = x"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_zipperposition: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_e: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_vampire: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_spass: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_cvc5: "(\<lambda>x::nat. 0)((b::nat) := 1) b = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end