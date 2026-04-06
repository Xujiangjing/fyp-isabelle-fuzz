theory A_conn_xor
imports Main
begin


lemma test_conn_xor: "(xor::nat) = xor"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
