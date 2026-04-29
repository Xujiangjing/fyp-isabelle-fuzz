theory A_type_int
imports Main
begin


lemma test_type_int: "(x::int) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
