theory A_role_plain
imports Main
begin


lemma test_role_plain: "(plain::nat) = plain"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
