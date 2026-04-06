theory A_type_bool
imports Main
begin


lemma test_type_bool: "(x::bool) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
