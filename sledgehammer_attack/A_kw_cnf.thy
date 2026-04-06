theory A_kw_cnf
imports Main
begin


lemma test_kw_cnf: "(cnf::nat) = cnf"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
