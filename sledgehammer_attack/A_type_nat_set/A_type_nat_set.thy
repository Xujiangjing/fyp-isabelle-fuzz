theory A_type_nat_set
imports Main
begin


lemma test_type_nat_set: "(x::nat set) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
