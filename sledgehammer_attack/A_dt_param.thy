theory A_dt_param
imports Main
begin

datatype 'a mylist = Nil | Cons 'a "'a mylist"

lemma test_dt_param: "Nil \<noteq> Cons (0::nat) Nil"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
