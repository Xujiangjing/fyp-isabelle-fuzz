theory HO_Format_Bug
  imports Main
begin

lemma test_e_1: "(f :: nat => nat) x = f x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  by simp

lemma test_vampire_1: "(f :: nat => nat) x = f x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  by simp

lemma test_zipper_1: "(f :: nat => nat) x = f x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  by simp

lemma test_e_2: "((\<lambda>y::nat. f y) x) = f x"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  by simp

lemma test_vampire_2: "((\<lambda>y::nat. f y) x) = f x"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  by simp

lemma test_zipper_2: "((\<lambda>y::nat. f y) x) = f x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  by simp

lemma test_e_3: "map (f :: nat => nat) [x] = [f x]"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  by simp

lemma test_vampire_3: "map (f :: nat => nat) [x] = [f x]"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  by simp

lemma test_zipper_3: "map (f :: nat => nat) [x] = [f x]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  by simp

definition fof_val :: nat where "fof_val = 0"
definition tff_val :: nat where "tff_val = 0"
definition thf_val :: nat where "thf_val = 0"

lemma test_name_e: "fof_val + tff_val = tff_val + fof_val"
  sledgehammer [prover = e, slices = 1, timeout = 30, overlord]
  by (simp add: fof_val_def tff_val_def)

lemma test_name_vampire: "fof_val + tff_val = tff_val + fof_val"
  sledgehammer [prover = vampire, slices = 1, timeout = 30, overlord]
  by (simp add: fof_val_def tff_val_def)

lemma test_name_zipper: "fof_val + tff_val = tff_val + fof_val"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  by (simp add: fof_val_def tff_val_def)

end
