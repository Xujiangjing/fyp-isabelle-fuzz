theory A_primrec_len
imports Main
begin

primrec mylen :: "'a list \<Rightarrow> nat" where
  "mylen [] = 0"
| "mylen (x # xs) = Suc (mylen xs)"

lemma test_primrec_len: "mylen [] = (0::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
