theory A_dt_color
imports Main
begin

datatype color = Red | Green | Blue

lemma test_dt_color: "\<forall>c::color. c = Red \<or> c = Green \<or> c = Blue"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
