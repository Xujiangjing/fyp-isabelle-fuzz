theory A_dollar_quotient
imports Main
begin


lemma test_dollar_quotient: "(quotient::nat) = quotient"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
