theory SymbolEscape
imports Main
begin

lemma conn_1: "not = (not::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_2: "and = (and::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_3: "or = (or::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_4: "implies = (implies::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_5: "iff = (iff::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_6: "xor = (xor::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_7: "forall = (forall::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_8: "exists = (exists::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_9: "lambda = (lambda::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_10: "equal = (equal::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma conn_11: "apply = (apply::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_12: "axiom = (axiom::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_13: "hypothesis = (hypothesis::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_14: "definition = (definition::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_15: "lemma = (lemma::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_16: "theorem = (theorem::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_17: "conjecture = (conjecture::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_18: "negated_conjecture = (negated_conjecture::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma role_19: "plain = (plain::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_20: "true = (true::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_21: "false = (false::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_22: "ite = (ite::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_23: "let = (let::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_24: "sum = (sum::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_25: "product = (product::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_26: "difference = (difference::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma dollar_27: "quotient = (quotient::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_28: "x_prime = (x_prime::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_29: "x_y_z = (x_y_z::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_30: "ab = (ab::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_31: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa = (aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_32: "O = (O::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_33: "I = (I::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_34: "T = (T::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma special_35: "int = (int::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

end