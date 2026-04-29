theory A_mp_comm_zipperposition
imports Main
begin


lemma test_mp_comm_zipperposition: "(x::nat) + y = y + x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
