theory A_shadow_nat
imports Main
begin


lemma test_shadow_nat: "(nat::nat) = nat"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
