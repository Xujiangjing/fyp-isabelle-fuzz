#!/bin/bash
# generate_smt_seeds.sh
# Run from your Isabelle working directory.
# Creates multiple .thy files, runs Sledgehammer in overlord mode,
# and collects the generated .smt_in files into ~/smt_seeds/

SEED_DIR="$HOME/smt_seeds"
THY_DIR="$HOME/smt_seed_theories"
ISABELLE_PROB_DIR="$HOME/.isabelle/Isabelle2025"

mkdir -p "$SEED_DIR"
mkdir -p "$THY_DIR"

# ── Write theory files ──────────────────────────────────────────────

cat > "$THY_DIR/SMT_Seed_Nat.thy" << 'EOF'
theory SMT_Seed_Nat
  imports Main
begin

(* Natural number arithmetic — commutativity, associativity, distributivity *)
lemma nat_add_comm: "(x::nat) + y = y + x"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma nat_mul_comm: "(x::nat) * y = y * x"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma nat_add_assoc: "((x::nat) + y) + z = x + (y + z)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma nat_distrib: "(x::nat) * (y + z) = x * y + x * z"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma nat_zero_ident: "(x::nat) + 0 = x"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma nat_le_add: "(x::nat) \<le> x + y"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Int.thy" << 'EOF'
theory SMT_Seed_Int
  imports Main
begin

(* Integer arithmetic — negation, subtraction, abs *)
lemma int_neg_neg: "- (- (x::int)) = x"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma int_add_neg: "(x::int) + (- x) = 0"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma int_sub_self: "(x::int) - x = 0"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma int_abs_nonneg: "\<bar>x::int\<bar> \<ge> 0"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma int_triangle: "\<bar>(x::int) + y\<bar> \<le> \<bar>x\<bar> + \<bar>y\<bar>"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma int_mul_sign: "(x::int) * x \<ge> 0"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_List.thy" << 'EOF'
theory SMT_Seed_List
  imports Main
begin

(* List operations — append, rev, length, map, filter *)
lemma list_append_nil: "xs @ [] = (xs :: 'a list)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma list_append_assoc: "(xs @ ys) @ zs = xs @ (ys @ (zs :: 'a list))"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma list_rev_rev: "rev (rev xs) = (xs :: 'a list)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma list_length_append: "length (xs @ ys) = length xs + length (ys :: 'a list)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma list_rev_length: "length (rev xs) = length (xs :: 'a list)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma list_map_append: "map f (xs @ ys) = map f xs @ map f (ys :: 'a list)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Set.thy" << 'EOF'
theory SMT_Seed_Set
  imports Main
begin

(* Set operations — union, inter, subset, membership *)
lemma set_union_comm: "(A :: 'a set) \<union> B = B \<union> A"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma set_inter_comm: "(A :: 'a set) \<inter> B = B \<inter> A"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma set_union_assoc: "((A :: 'a set) \<union> B) \<union> C = A \<union> (B \<union> C)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma set_subset_union: "(A :: 'a set) \<subseteq> A \<union> B"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma set_inter_subset: "(A :: 'a set) \<inter> B \<subseteq> A"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma set_demorgan: "- ((A :: 'a set) \<union> B) = (- A) \<inter> (- B)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Fun.thy" << 'EOF'
theory SMT_Seed_Fun
  imports Main
begin

(* Function composition, identity, injectivity *)
lemma fun_comp_assoc: "f \<circ> (g \<circ> h) = (f \<circ> g) \<circ> (h :: 'a \<Rightarrow> 'b)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma fun_id_left: "id \<circ> f = (f :: 'a \<Rightarrow> 'b)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma fun_id_right: "f \<circ> id = (f :: 'a \<Rightarrow> 'b)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma fun_inj_comp: "\<lbrakk>inj f; inj g\<rbrakk> \<Longrightarrow> inj (f \<circ> (g :: 'a \<Rightarrow> 'b))"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Option.thy" << 'EOF'
theory SMT_Seed_Option
  imports Main
begin

(* Option type — None, Some, map_option, bind *)
lemma option_map_none: "map_option f None = (None :: 'b option)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma option_map_some: "map_option f (Some x) = Some (f x)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma option_the_some: "the (Some x) = (x :: 'a)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma option_case_some: "(case Some x of None \<Rightarrow> d | Some y \<Rightarrow> f y) = f (x :: 'a)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Div.thy" << 'EOF'
theory SMT_Seed_Div
  imports Main
begin

(* Integer division and modulo — edge cases that stress SMT solvers *)
lemma div_pos: "b > 0 \<Longrightarrow> (a::int) = b * (a div b) + (a mod b)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma mod_range: "b > 0 \<Longrightarrow> 0 \<le> (a::int) mod b \<and> a mod b < b"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma div_by_one: "(a::int) div 1 = a"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma mod_by_one: "(a::int) mod 1 = 0"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma div_self: "a \<noteq> 0 \<Longrightarrow> (a::int) div a = 1"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Quant.thy" << 'EOF'
theory SMT_Seed_Quant
  imports Main
begin

(* Quantifier-heavy — existentials, nested quantifiers, Hilbert choice *)
lemma quant_swap: "(\<forall>x::nat. \<forall>y. P x y) = (\<forall>y. \<forall>x. P x y)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma quant_exists_conj:
  "\<exists>(x::nat). P x \<and> Q x \<Longrightarrow> (\<exists>x. P x) \<and> (\<exists>x. Q x)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma quant_demorgan:
  "(\<not> (\<forall>(x::nat). P x)) = (\<exists>x. \<not> P x)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma quant_forall_imp:
  "\<lbrakk>\<forall>(x::nat). P x \<longrightarrow> Q x; \<forall>x. P x\<rbrakk> \<Longrightarrow> \<forall>x. Q x"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma quant_witness:
  "\<exists>(x::nat). P x \<Longrightarrow> P (SOME x. P x)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Bool.thy" << 'EOF'
theory SMT_Seed_Bool
  imports Main
begin

(* Boolean logic — de Morgan, excluded middle, double negation *)
lemma bool_demorgan1: "\<not>(P \<and> Q) = (\<not>P \<or> \<not>Q)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma bool_demorgan2: "\<not>(P \<or> Q) = (\<not>P \<and> \<not>Q)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma bool_excluded_middle: "P \<or> \<not>P"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma bool_double_neg: "\<not>\<not>P = P"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma bool_imp_disj: "(P \<longrightarrow> Q) = (\<not>P \<or> Q)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma bool_contra: "\<lbrakk>P; \<not>P\<rbrakk> \<Longrightarrow> False"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

cat > "$THY_DIR/SMT_Seed_Pair.thy" << 'EOF'
theory SMT_Seed_Pair
  imports Main
begin

(* Product types — fst, snd, swap *)
lemma pair_fst: "fst (a, b) = (a :: 'a)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma pair_snd: "snd (a, b) = (b :: 'b)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma pair_eq: "((a::'a) = c \<and> (b::'b) = d) \<Longrightarrow> (a, b) = (c, d)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma pair_swap_swap: "prod.swap (prod.swap p) = (p :: 'a \<times> 'b)"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

lemma pair_surjective: "p = (fst p, snd (p :: 'a \<times> 'b))"
  sledgehammer [provers = z3 cvc5, timeout = 10, overlord]
  oops

end
EOF

echo "═══════════════════════════════════════════"
echo " Generated theory files in $THY_DIR:"
ls "$THY_DIR"/*.thy
echo "═══════════════════════════════════════════"
echo ""
echo "Now run each theory one at a time in Isabelle/jEdit or via CLI."
echo "After each run, collect the generated .smt_in files:"
echo ""
echo "  cp $ISABELLE_PROB_DIR/prob_z3*.smt_in $SEED_DIR/"
echo "  cp $ISABELLE_PROB_DIR/prob_cvc5*.smt_in $SEED_DIR/"
echo ""
echo "Or use the batch runner below..."
echo ""

# ── Batch runner (optional, runs isabelle build) ────────────────────

cat > "$THY_DIR/ROOT" << 'ROOTEOF'
session SMT_Seeds = HOL +
  theories
    SMT_Seed_Nat
    SMT_Seed_Int
    SMT_Seed_List
    SMT_Seed_Set
    SMT_Seed_Fun
    SMT_Seed_Option
    SMT_Seed_Div
    SMT_Seed_Quant
    SMT_Seed_Bool
    SMT_Seed_Pair
ROOTEOF

echo "To run all theories at once:"
echo ""
echo "  cd $THY_DIR"
echo "  isabelle build -o sledgehammer_provers=z3,cvc5 -D ."
echo ""
echo "Then collect seeds:"
echo ""
echo "  for f in $ISABELLE_PROB_DIR/prob_*.smt_in; do"
echo "    base=\$(basename \"\$f\")"
echo "    cp \"\$f\" \"$SEED_DIR/\${base}\""
echo "  done"
echo ""
echo "  ls $SEED_DIR/"
