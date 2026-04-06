theory A_type_option_list
imports Main
begin


lemma test_type_option_list: "(x::nat option list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
