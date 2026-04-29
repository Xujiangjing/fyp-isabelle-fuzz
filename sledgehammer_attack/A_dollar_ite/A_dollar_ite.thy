theory A_dollar_ite
imports Main
begin


lemma test_dollar_ite: "(ite::nat) = ite"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
