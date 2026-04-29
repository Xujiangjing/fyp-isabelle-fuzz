theory A_type_list_list
imports Main
begin


lemma test_type_list_list: "(x::nat list list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
