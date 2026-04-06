theory A_mp_refl_e
imports Main
begin


lemma test_mp_refl_e: "(x::nat) = x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end
