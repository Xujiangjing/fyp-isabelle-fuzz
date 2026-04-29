theory A_mp_comm_vampire
imports Main
begin


lemma test_mp_comm_vampire: "(x::nat) + y = y + x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end
