theory A_ite_simple
imports Main
begin


lemma test_ite_simple: "(if True then (x::nat) else 0) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
