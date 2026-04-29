theory A_kw_fof
imports Main
begin


lemma test_kw_fof: "(fof::nat) = fof"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
