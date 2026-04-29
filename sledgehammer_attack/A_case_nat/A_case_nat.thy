theory A_case_nat
imports Main
begin


lemma test_case_nat: "(case (0::nat) of 0 \<Rightarrow> True | Suc n \<Rightarrow> False)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
