theory A_role_axiom
imports Main
begin


lemma test_role_axiom: "(axiom::nat) = axiom"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
