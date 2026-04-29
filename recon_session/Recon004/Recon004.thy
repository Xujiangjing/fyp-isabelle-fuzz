theory Recon004
imports Main
begin

lemma int_arith__medium__1_zipperposition: "(m::int) * (-1) = -m"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_e: "(m::int) * (-1) = -m"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_vampire: "(m::int) * (-1) = -m"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_spass: "(m::int) * (-1) = -m"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma int_arith__medium__1_cvc5: "(m::int) * (-1) = -m"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_zipperposition: "fst (y, n) = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_e: "fst (y, n) = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_vampire: "fst (y, n) = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_spass: "fst (y, n) = (y::nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma pair__simple__2_cvc5: "fst (y, n) = (y::nat)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_zipperposition: "min (w::nat) w = w"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_e: "min (w::nat) w = w"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_vampire: "min (w::nat) w = w"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_spass: "min (w::nat) w = w"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma nat_arith__simple__3_cvc5: "min (w::nat) w = w"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__4_zipperposition: "(v::nat) mod 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__4_e: "(v::nat) mod 1 = 0"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__4_vampire: "(v::nat) mod 1 = 0"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__4_spass: "(v::nat) mod 1 = 0"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma divmod__medium__4_cvc5: "(v::nat) mod 1 = 0"
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

lemma power__simple__6_zipperposition: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__6_e: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__6_vampire: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__6_spass: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma power__simple__6_cvc5: "(2::nat) ^ 0 = 1"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma set__hard__7_zipperposition: "set [u] \<inter> set [u, a] = set [(u::nat)]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma set__hard__7_e: "set [u] \<inter> set [u, a] = set [(u::nat)]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma set__hard__7_vampire: "set [u] \<inter> set [u, a] = set [(u::nat)]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma set__hard__7_spass: "set [u] \<inter> set [u, a] = set [(u::nat)]"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma set__hard__7_cvc5: "set [u] \<inter> set [u, a] = set [(u::nat)]"
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

lemma option__simple__9_zipperposition: "\<not> Option.is_none (Some (u::nat))"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_e: "\<not> Option.is_none (Some (u::nat))"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_vampire: "\<not> Option.is_none (Some (u::nat))"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_spass: "\<not> Option.is_none (Some (u::nat))"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma option__simple__9_cvc5: "\<not> Option.is_none (Some (u::nat))"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_zipperposition: "(if False then (w::nat) else v) = v"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_e: "(if False then (w::nat) else v) = v"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_vampire: "(if False then (w::nat) else v) = v"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_spass: "(if False then (w::nat) else v) = v"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma ite__simple__10_cvc5: "(if False then (w::nat) else v) = v"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_zipperposition: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_e: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_vampire: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_spass: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma logic__simple__11_cvc5: "(\<forall>x::nat. x = x)"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_zipperposition: "(\<lambda>x::nat. x) a = a"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_e: "(\<lambda>x::nat. x) a = a"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_vampire: "(\<lambda>x::nat. x) a = a"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_spass: "(\<lambda>x::nat. x) a = a"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma hof__simple__12_cvc5: "(\<lambda>x::nat. x) a = a"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__13_zipperposition: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__13_e: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__13_vampire: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__13_spass: "isl (Inl (m::nat) :: nat + nat)"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma sum__simple__13_cvc5: "isl (Inl (m::nat) :: nat + nat)"
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

lemma recursive__medium__15_zipperposition: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_e: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_vampire: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_spass: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = spass, slices = 1, timeout = 30, overlord]
  oops

lemma recursive__medium__15_cvc5: "length (replicate 5 (0::nat)) = 5"
  sledgehammer [prover = cvc5, slices = 1, timeout = 30, overlord]
  oops

end