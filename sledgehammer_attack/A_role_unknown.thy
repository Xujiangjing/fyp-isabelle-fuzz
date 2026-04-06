theory A_role_unknown
imports Main
begin


lemma test_role_unknown: "(unknown::nat) = unknown"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
