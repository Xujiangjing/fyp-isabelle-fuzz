theory A_conn_apply
imports Main
begin


lemma test_conn_apply: "(apply::nat) = apply"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
