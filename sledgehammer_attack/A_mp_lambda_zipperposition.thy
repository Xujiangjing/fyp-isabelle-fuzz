theory A_mp_lambda_zipperposition
imports Main
begin


lemma test_mp_lambda_zipperposition: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
