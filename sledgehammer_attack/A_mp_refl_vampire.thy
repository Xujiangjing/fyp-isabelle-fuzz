theory A_mp_refl_vampire
imports Main
begin


lemma test_mp_refl_vampire: "(x::nat) = x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end
