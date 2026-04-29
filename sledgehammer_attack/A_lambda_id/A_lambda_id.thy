theory A_lambda_id
imports Main
begin


lemma test_lambda_id: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
