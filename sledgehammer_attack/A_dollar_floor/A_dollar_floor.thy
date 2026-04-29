theory A_dollar_floor
imports Main
begin


lemma test_dollar_floor: "(floor::nat) = floor"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
