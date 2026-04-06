theory A_nested_quant
imports Main
begin


lemma test_nested_quant: "\<forall>x::nat. \<exists>y::nat. y = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
