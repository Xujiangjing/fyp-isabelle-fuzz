theory A_set_member
imports Main
begin


lemma test_set_member: "(x::nat) \<in> set [x, y]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
