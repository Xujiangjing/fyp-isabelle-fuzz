theory Recon016
imports Main
begin

lemma option__simple__1_zipperposition: "\<not> Option.is_none (Some (x::nat))"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_e: "\<not> Option.is_none (Some (x::nat))"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_vampire: "\<not> Option.is_none (Some (x::nat))"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_spass: "\<not> Option.is_none (Some (x::nat))"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__1_cvc5: "\<not> Option.is_none (Some (x::nat))"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__2_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__2_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__2_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__2_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__2_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__3_zipperposition: "(n::nat) mod 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__3_e: "(n::nat) mod 1 = 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__3_vampire: "(n::nat) mod 1 = 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__3_spass: "(n::nat) mod 1 = 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__3_cvc5: "(n::nat) mod 1 = 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__4_zipperposition: "(if (w::nat) = w then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__4_e: "(if (w::nat) = w then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__4_vampire: "(if (w::nat) = w then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__4_spass: "(if (w::nat) = w then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__4_cvc5: "(if (w::nat) = w then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__5_zipperposition: "(b::nat) + w = w + b"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__5_e: "(b::nat) + w = w + b"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__5_vampire: "(b::nat) + w = w + b"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__5_spass: "(b::nat) + w = w + b"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__5_cvc5: "(b::nat) + w = w + b"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_zipperposition: "(1::nat) ^ m = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_e: "(1::nat) ^ m = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_vampire: "(1::nat) ^ m = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_spass: "(1::nat) ^ m = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__medium__6_cvc5: "(1::nat) ^ m = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__7_zipperposition: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__7_e: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__7_vampire: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__7_spass: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__7_cvc5: "(\<lambda>x::nat. 0)((m::nat) := 1) m = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_zipperposition: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_e: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_vampire: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_spass: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__8_cvc5: "\<not> isl (Inr (m::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__9_zipperposition: "card (set [(v::nat)]) \<le> 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__9_e: "card (set [(v::nat)]) \<le> 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__9_vampire: "card (set [(v::nat)]) \<le> 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__9_spass: "card (set [(v::nat)]) \<le> 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__medium__9_cvc5: "card (set [(v::nat)]) \<le> 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__10_zipperposition: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__10_e: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__10_vampire: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__10_spass: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__10_cvc5: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__11_zipperposition: "drop 1 [u, b] = [(b::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__11_e: "drop 1 [u, b] = [(b::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__11_vampire: "drop 1 [u, b] = [(b::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__11_spass: "drop 1 [u, b] = [(b::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__11_cvc5: "drop 1 [u, b] = [(b::nat)]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__12_zipperposition: "fst (a, y) = (a::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__12_e: "fst (a, y) = (a::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__12_vampire: "fst (a, y) = (a::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__12_spass: "fst (a, y) = (a::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__12_cvc5: "fst (a, y) = (a::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__13_zipperposition: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__13_e: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__13_vampire: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__13_spass: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__13_cvc5: "(let x = (u::nat) in x + 1) = u + 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__14_zipperposition: "(a::int) - a = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__14_e: "(a::int) - a = 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__14_vampire: "(a::int) - a = 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__14_spass: "(a::int) - a = 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__simple__14_cvc5: "(a::int) - a = 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__15_zipperposition: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__15_e: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__15_vampire: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__15_spass: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__medium__15_cvc5: "filter (\<lambda>x. True) [(1::nat)] = [1]"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end