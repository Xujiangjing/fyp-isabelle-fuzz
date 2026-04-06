theory A_list_rev
imports Main
begin


lemma test_list_rev: "rev (rev xs) = (xs::nat list)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
