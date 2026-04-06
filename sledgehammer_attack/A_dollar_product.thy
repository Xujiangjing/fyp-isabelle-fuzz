theory A_dollar_product
imports Main
begin


lemma test_dollar_product: "(product::nat) = product"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
