theory A_kw_pair_fof_tff
imports Main
begin


lemma test_kw_pair_fof_tff: "(fof::nat) + tff = tff + fof"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
