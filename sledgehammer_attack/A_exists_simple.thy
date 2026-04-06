theory A_exists_simple
imports Main
begin


lemma test_exists_simple: "\<exists>x::nat. x = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
