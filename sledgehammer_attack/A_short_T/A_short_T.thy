theory A_short_T
imports Main
begin


lemma test_short_T: "(T::nat) = T"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
