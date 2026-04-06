theory A_dollar_ceiling
imports Main
begin


lemma test_dollar_ceiling: "(ceiling::nat) = ceiling"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
