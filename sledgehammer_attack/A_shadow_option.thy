theory A_shadow_option
imports Main
begin


lemma test_shadow_option: "(option::nat) = option"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
