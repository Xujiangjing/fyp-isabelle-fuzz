theory A_type_int_list
imports Main
begin


lemma test_type_int_list: "(x::int list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
