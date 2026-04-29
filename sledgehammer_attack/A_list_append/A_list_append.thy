theory A_list_append
imports Main
begin


lemma test_list_append: "length (xs @ ys) = length xs + length (ys::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
