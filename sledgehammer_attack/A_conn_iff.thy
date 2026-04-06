theory A_conn_iff
imports Main
begin


lemma test_conn_iff: "(iff::nat) = iff"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
