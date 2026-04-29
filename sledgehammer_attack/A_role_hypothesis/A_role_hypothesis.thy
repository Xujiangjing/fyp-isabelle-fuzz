theory A_role_hypothesis
imports Main
begin


lemma test_role_hypothesis: "(hypothesis::nat) = hypothesis"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
