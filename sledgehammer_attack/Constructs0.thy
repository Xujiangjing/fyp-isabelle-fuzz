theory Constructs0
imports Main
begin

(* === Attack surface: record_simple === *)

record point = xcoord :: nat  ycoord :: nat

lemma point_eq_0: "xcoord (\<lparr> xcoord = 1, ycoord = 2 \<rparr>) = (1::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


(* === Attack surface: class_instance === *)

class myord =
  fixes mylt :: "'a \<Rightarrow> 'a \<Rightarrow> bool"

instantiation nat :: myord
begin
definition mylt_nat :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "mylt_nat x y = (x < y)"
instance ..
end

lemma mylt_test_1: "mylt (0::nat) 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


(* === Attack surface: datatype_recursive === *)

datatype nat_tree = Leaf | Node nat_tree nat nat_tree

lemma tree_leaf_2: "Leaf \<noteq> Node Leaf (0::nat) Leaf"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


(* === Attack surface: datatype_simple === *)

datatype color = Red | Green | Blue

lemma color_exhaust_3: "\<forall>c::color. c = Red \<or> c = Green \<or> c = Blue"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops


end