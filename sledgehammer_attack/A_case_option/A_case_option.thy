theory A_case_option
imports Main
begin


lemma test_case_option: "(case Some (x::nat) of None \<Rightarrow> 0 | Some v \<Rightarrow> v) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
