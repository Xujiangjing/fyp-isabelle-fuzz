theory A_mp_lambda_e
imports Main
begin


lemma test_mp_lambda_e: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end
