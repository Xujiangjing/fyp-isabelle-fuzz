theory A_conn_implies
imports Main
begin


lemma test_conn_implies: "(implies::nat) = implies"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
