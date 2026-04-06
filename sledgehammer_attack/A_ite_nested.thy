theory A_ite_nested
imports Main
begin


lemma test_ite_nested: "(if True then (if False then 0 else (x::nat)) else 0) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
