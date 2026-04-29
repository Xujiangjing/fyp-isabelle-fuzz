theory A_mp_kw_fof_vampire
imports Main
begin


lemma test_mp_kw_fof_vampire: "(fof::nat) = fof"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end
