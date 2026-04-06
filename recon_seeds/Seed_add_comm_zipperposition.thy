theory Seed_add_comm_zipperposition
imports Main
begin

lemma add_comm: "(x::nat) + y = y + x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end