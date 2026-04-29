theory A_bool_eq
imports Main
begin


lemma test_bool_eq: "((x::nat) = y) = ((y::nat) = x)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
