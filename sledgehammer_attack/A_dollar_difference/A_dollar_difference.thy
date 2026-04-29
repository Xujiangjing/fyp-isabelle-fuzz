theory A_dollar_difference
imports Main
begin


lemma test_dollar_difference: "(difference::nat) = difference"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
