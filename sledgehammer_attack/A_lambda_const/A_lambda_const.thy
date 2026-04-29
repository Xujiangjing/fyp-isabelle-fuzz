theory A_lambda_const
imports Main
begin


lemma test_lambda_const: "(\<lambda>x::nat. 0) y = (0::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
