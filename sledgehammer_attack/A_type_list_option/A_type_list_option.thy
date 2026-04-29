theory A_type_list_option
imports Main
begin


lemma test_type_list_option: "(x::nat list option) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
