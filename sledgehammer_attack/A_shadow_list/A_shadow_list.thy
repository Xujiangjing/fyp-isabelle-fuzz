theory A_shadow_list
imports Main
begin


lemma test_shadow_list: "(list::nat) = list"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
