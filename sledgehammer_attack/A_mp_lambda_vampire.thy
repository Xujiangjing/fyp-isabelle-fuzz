theory A_mp_lambda_vampire
imports Main
begin


lemma test_mp_lambda_vampire: "(\<lambda>x::nat. x) y = (y::nat)"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end
