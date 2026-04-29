theory A_let_simple
imports Main
begin


lemma test_let_simple: "(let y = (x::nat) in y) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
