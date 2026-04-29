theory A_kw_include
imports Main
begin


lemma test_kw_include: "(include::nat) = include"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
