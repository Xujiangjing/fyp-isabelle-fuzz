theory Seed_mem_set_zipperposition
imports Main
begin

lemma mem_set: "(x::nat) \<in> set [x, y]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end