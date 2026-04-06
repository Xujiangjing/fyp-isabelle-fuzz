theory A_mp_refl_zipperposition
imports Main
begin


lemma test_mp_refl_zipperposition: "(x::nat) = x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
