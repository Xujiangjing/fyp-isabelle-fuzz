theory A_short_I
imports Main
begin


lemma test_short_I: "(I::nat) = I"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
