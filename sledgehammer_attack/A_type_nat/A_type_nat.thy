theory A_type_nat
imports Main
begin


lemma test_type_nat: "(x::nat) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
