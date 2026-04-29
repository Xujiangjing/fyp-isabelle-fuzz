theory A_mp_kw_fof_zipperposition
imports Main
begin


lemma test_mp_kw_fof_zipperposition: "(fof::nat) = fof"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
