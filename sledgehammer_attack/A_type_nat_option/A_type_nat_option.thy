theory A_type_nat_option
imports Main
begin


lemma test_type_nat_option: "(x::nat option) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
