theory A_lambda_nested
imports Main
begin


lemma test_lambda_nested: "(\<lambda>x::nat. \<lambda>y::nat. x + y) a b = a + (b::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
