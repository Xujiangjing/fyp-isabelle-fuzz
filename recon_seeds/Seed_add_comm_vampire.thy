theory Seed_add_comm_vampire
imports Main
begin

lemma add_comm: "(x::nat) + y = y + x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  oops

end