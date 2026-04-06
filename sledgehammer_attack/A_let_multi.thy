theory A_let_multi
imports Main
begin


lemma test_let_multi: "(let y = (x::nat); z = y in z) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
