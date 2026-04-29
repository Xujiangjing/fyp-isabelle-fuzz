theory A_mp_kw_fof_e
imports Main
begin


lemma test_mp_kw_fof_e: "(fof::nat) = fof"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end
