theory A_type_poly_a
imports Main
begin


lemma test_type_poly_a: "(x::'a) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
