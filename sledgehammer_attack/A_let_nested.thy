theory A_let_nested
imports Main
begin


lemma test_let_nested: "(let y = (let z = (x::nat) in z) in y) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
