theory A_dollar_uminus
imports Main
begin


lemma test_dollar_uminus: "(uminus::nat) = uminus"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
