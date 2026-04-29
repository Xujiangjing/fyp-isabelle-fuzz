theory A_type_prod
imports Main
begin


lemma test_type_prod: "fst (a, b) = (a::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
