theory A_dt_tree
imports Main
begin

datatype nat_tree = Leaf | Node nat_tree nat nat_tree

lemma test_dt_tree: "Leaf \<noteq> Node Leaf (0::nat) Leaf"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
