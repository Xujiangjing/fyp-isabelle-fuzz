theory A_div_nat
imports Main
begin


lemma test_div_nat: "(6::nat) div 2 = 3"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
