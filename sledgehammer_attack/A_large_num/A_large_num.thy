theory A_large_num
imports Main
begin


lemma test_large_num: "(2147483647::nat) + 1 = 2147483648"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
