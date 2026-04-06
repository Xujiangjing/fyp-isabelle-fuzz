theory A_dollar_sum
imports Main
begin


lemma test_dollar_sum: "(sum::nat) = sum"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
