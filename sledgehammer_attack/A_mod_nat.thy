theory A_mod_nat
imports Main
begin


lemma test_mod_nat: "(7::nat) mod 3 = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
