theory A_type_poly_fun
imports Main
begin


lemma test_type_poly_fun: "(f::'a \<Rightarrow> 'b) = f"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 30, overlord]
  oops

end
