theory A_forall_simple
imports Main
begin


lemma test_forall_simple: "\<forall>x::nat. x + 0 = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
