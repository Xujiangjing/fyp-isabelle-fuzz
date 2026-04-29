theory A_shadow_set
imports Main
begin


lemma test_shadow_set: "(set::nat) = set"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
