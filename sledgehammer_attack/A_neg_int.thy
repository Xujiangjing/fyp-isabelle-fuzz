theory A_neg_int
imports Main
begin


lemma test_neg_int: "(- (1::int)) + 1 = 0"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
