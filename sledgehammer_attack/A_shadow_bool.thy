theory A_shadow_bool
imports Main
begin


lemma test_shadow_bool: "(bool::nat) = bool"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
