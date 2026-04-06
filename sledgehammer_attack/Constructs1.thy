theory Constructs1
imports Main
begin

(* === Attack surface: datatype_simple === *)

datatype color = Red | Green | Blue

lemma color_exhaust_0: "\<forall>c::color. c = Red \<or> c = Green \<or> c = Blue"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


(* === Attack surface: primrec_simple === *)

primrec mylen :: "'a list \<Rightarrow> nat" where
  "mylen [] = 0"
| "mylen (x # xs) = Suc (mylen xs)"

lemma mylen_nil_1: "mylen [] = (0::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


(* === Attack surface: record_simple === *)

record point = xcoord :: nat  ycoord :: nat

lemma point_eq_2: "xcoord (\<lparr> xcoord = 1, ycoord = 2 \<rparr>) = (1::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


(* === Attack surface: datatype_recursive === *)

datatype nat_tree = Leaf | Node nat_tree nat nat_tree

lemma tree_leaf_3: "Leaf \<noteq> Node Leaf (0::nat) Leaf"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


end