theory A_case_list
imports Main
begin


lemma test_case_list: "(case [x::nat] of [] \<Rightarrow> 0 | y # ys \<Rightarrow> y) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
