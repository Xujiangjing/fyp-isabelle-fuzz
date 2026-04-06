theory R005_Mut002
imports Main
begin

lemma mut_1: "(l8::string) * (l8 + 1) = l8 * l8 + l8"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_2: "(k9::bool) + r9 = r9 + k9"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_3: "min (j8::int list) r7 <= max j8 r7"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_4: "(n9::char) * (u3 + 1) = n9 * u3 + n9"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

lemma mut_5: "sorted (sort [(tcf::char), tff1])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 5, overlord]
  oops

end