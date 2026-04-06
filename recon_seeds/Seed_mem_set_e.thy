theory Seed_mem_set_e
imports Main
begin

lemma mem_set: "(x::nat) \<in> set [x, y]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  oops

end