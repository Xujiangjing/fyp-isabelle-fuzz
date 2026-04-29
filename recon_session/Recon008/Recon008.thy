theory Recon008
imports Main
begin

lemma logic__simple__1_zipperposition: "\<not> False"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_e: "\<not> False"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_vampire: "\<not> False"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_spass: "\<not> False"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__1_cvc5: "\<not> False"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__2_zipperposition: "\<bar>(v::int)\<bar> \<ge> 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__2_e: "\<bar>(v::int)\<bar> \<ge> 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__2_vampire: "\<bar>(v::int)\<bar> \<ge> 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__2_spass: "\<bar>(v::int)\<bar> \<ge> 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__2_cvc5: "\<bar>(v::int)\<bar> \<ge> 0"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_zipperposition: "(let x = (u::nat); y = a in x + y) = u + a"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_e: "(let x = (u::nat); y = a in x + y) = u + a"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_vampire: "(let x = (u::nat); y = a in x + y) = u + a"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_spass: "(let x = (u::nat); y = a in x + y) = u + a"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma let__medium__3_cvc5: "(let x = (u::nat); y = a in x + y) = u + a"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__4_zipperposition: "(\<lambda>x::nat. x) z = z"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__4_e: "(\<lambda>x::nat. x) z = z"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__4_vampire: "(\<lambda>x::nat. x) z = z"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__4_spass: "(\<lambda>x::nat. x) z = z"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__4_cvc5: "(\<lambda>x::nat. x) z = z"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__5_zipperposition: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__5_e: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__5_vampire: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__5_spass: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__5_cvc5: "\<not> Option.is_none (Some (b::nat))"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__6_zipperposition: "v = (v::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__6_e: "v = (v::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__6_vampire: "v = (v::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__6_spass: "v = (v::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__simple__6_cvc5: "v = (v::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_zipperposition: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_e: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_vampire: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_spass: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__7_cvc5: "sum_list [(1::nat), 2, 3] = 6"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__8_zipperposition: "(n::nat) + n = 2 * n"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__8_e: "(n::nat) + n = 2 * n"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__8_vampire: "(n::nat) + n = 2 * n"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__8_spass: "(n::nat) + n = 2 * n"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__medium__8_cvc5: "(n::nat) + n = 2 * n"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__9_zipperposition: "(5::nat) mod 2 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__9_e: "(5::nat) mod 2 = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__9_vampire: "(5::nat) mod 2 = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__9_spass: "(5::nat) mod 2 = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__9_cvc5: "(5::nat) mod 2 = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_zipperposition: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_e: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_vampire: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_spass: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__10_cvc5: "\<not> isl (Inr (b::nat) :: nat + nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__11_zipperposition: "(if (x::nat) = x then 1 else 0) = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__11_e: "(if (x::nat) = x then 1 else 0) = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__11_vampire: "(if (x::nat) = x then 1 else 0) = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__11_spass: "(if (x::nat) = x then 1 else 0) = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__medium__11_cvc5: "(if (x::nat) = x then 1 else 0) = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__12_zipperposition: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__12_e: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__12_vampire: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__12_spass: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__12_cvc5: "(2::nat) ^ 1 = 2"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_zipperposition: "fst (y, x) = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_e: "fst (y, x) = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_vampire: "fst (y, x) = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_spass: "fst (y, x) = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__13_cvc5: "fst (y, x) = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__14_zipperposition: "nth [z, a] 1 = (a::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__14_e: "nth [z, a] 1 = (a::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__14_vampire: "nth [z, a] 1 = (a::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__14_spass: "nth [z, a] 1 = (a::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma list__medium__14_cvc5: "nth [z, a] 1 = (a::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_zipperposition: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_e: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_vampire: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_spass: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma fun__medium__15_cvc5: "(\<lambda>x::nat. 0)((u::nat) := 1) u = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end