theory A_record_point
imports Main
begin

record point =
  xcoord :: nat
  ycoord :: nat

lemma test_record_point: "xcoord (\<lparr> xcoord = 1, ycoord = 2 \<rparr>) = (1::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
