theory A_kw_thf
imports Main
begin


lemma test_kw_thf: "(thf::nat) = thf"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
