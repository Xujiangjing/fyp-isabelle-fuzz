theory A_role_conjecture
imports Main
begin


lemma test_role_conjecture: "(conjecture::nat) = conjecture"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
