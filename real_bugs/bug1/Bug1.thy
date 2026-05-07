theory Bug1 imports Main begin

lemma "tff = (tff :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30,verbose,overlord]
  oops

lemma "fof = (fof :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30,verbose,overlord]
  oops

lemma "include = (include :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30,verbose,overlord]
  oops

lemma "thf = (thf :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30,verbose,overlord]
  oops

lemma "cnf = (cnf :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30,verbose,overlord]
  by blast

(* Control: these should work fine *)
lemma "type = (type :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30]
  by blast
  

lemma "axiom = (axiom :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30]
  oops
 

end