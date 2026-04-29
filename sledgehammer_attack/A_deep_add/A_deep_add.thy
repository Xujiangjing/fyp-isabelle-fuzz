theory A_deep_add
imports Main
begin


lemma test_deep_add: "((((((x::nat) + 0) + 0) + 0) + 0) + 0) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
