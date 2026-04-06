theory Seed_add_comm_e
imports Main
begin

lemma add_comm: "(x::nat) + y = y + x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end