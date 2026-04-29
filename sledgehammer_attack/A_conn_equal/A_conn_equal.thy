theory A_conn_equal
imports Main
begin


lemma test_conn_equal: "(equal::nat) = equal"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
