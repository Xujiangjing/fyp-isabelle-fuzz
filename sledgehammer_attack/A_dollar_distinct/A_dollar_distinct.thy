theory A_dollar_distinct
imports Main
begin


lemma test_dollar_distinct: "(distinct::nat) = distinct"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
