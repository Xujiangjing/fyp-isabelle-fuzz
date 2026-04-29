theory A_shadow_int
imports Main
begin


lemma test_shadow_int: "(int::nat) = int"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
