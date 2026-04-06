theory A_short_O
imports Main
begin


lemma test_short_O: "(O::nat) = O"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
