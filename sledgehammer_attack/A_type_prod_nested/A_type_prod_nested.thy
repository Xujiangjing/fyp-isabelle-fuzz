theory A_type_prod_nested
imports Main
begin


lemma test_type_prod_nested: "fst (fst ((a, b), c)) = (a::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
