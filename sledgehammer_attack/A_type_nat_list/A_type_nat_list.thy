theory A_type_nat_list
imports Main
begin


lemma test_type_nat_list: "(x::nat list) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
