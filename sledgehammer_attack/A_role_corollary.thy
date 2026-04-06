theory A_role_corollary
imports Main
begin


lemma test_role_corollary: "(corollary::nat) = corollary"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
