theory A_kw_tff
imports Main
begin


lemma test_kw_tff: "(tff::nat) = tff"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
