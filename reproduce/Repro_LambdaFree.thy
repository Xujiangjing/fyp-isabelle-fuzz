(*
  Repro_LambdaFree.thy — Reproduce Zipperposition --check-lambda-free bugs from Isabelle.

  HOW TO USE:
    1. Open this file in Isabelle/jEdit (Isabelle 2025)
    2. Wait for Sledgehammer to run on each lemma
    3. Observe: Sledgehammer reports "no proof found" or times out
    4. Check the generated .p files (use overlord option to retain them)
    5. Run the .p files manually with:
         zipperposition --input tptp --output none --check-lambda-free only FILE.p
       to see the actual Failure(...) messages

  WHAT YOU WILL SEE IN ISABELLE:
    - Sledgehammer silently fails — it says "no proof found"
    - This is because Zipperposition crashes internally
    - The user has no way to know the real cause is an internal exception

  WHY THIS IS A BUG:
    - The .p files are valid TPTP (they parse fine in normal mode)
    - Zipperposition should gracefully reject out-of-fragment inputs
    - Instead it throws an uncaught Failure() exception
    - This causes Sledgehammer to silently lose a potential proof method
*)

theory Repro_LambdaFree
imports Main
begin

(* ================================================================
   SECTION 1: Lemmas that trigger Family A bugs
   (Argument of a term has out-of-fragment type)

   These involve type variables and polymorphic expressions that
   produce TPTP terms Zipperposition's lambda-free checker
   cannot handle gracefully.
   ================================================================ *)

(* Family A1: Type variable triggers — simple arithmetic *)
lemma family_a1_example_1: "x = (x::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma family_a1_example_2: "x + 0 = (x::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

(* Family A2: Skolem variable triggers — list operations *)
lemma family_a2_example_1: "length [(x::nat)] = 1"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma family_a2_example_2: "rev [(x::nat)] = [x]"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

(* Family A3: Internal symbol triggers — set/predicate operations *)
lemma family_a3_example_1: "hd [x] = (x::nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops


(* ================================================================
   SECTION 2: Lemmas likely to trigger Family B bugs
   (Tseitin encoding symbols)

   These involve logical connectives that cause Sledgehammer to
   generate Tseitin-encoded TPTP, which confuses the lambda-free
   checker.
   ================================================================ *)

lemma family_b_example_1: "(x::nat) + y = y + x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma family_b_example_2: "(x::nat) * (y + 1) = x * y + x"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops


(* ================================================================
   SECTION 3: Lemmas likely to trigger Family C bugs
   (Constant has out-of-fragment type)

   These involve algebraic structures (groups, monoids) whose
   background axioms contain types that the lambda-free checker
   rejects via internal exception rather than graceful rejection.
   ================================================================ *)

lemma family_c_example_1: "min (x::nat) y \<le> max x y"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma family_c_example_2: "sorted (sort [(x::nat), y])"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops


(* ================================================================
   SECTION 4: Parse error bug (TPTP keyword collision)

   When a free variable has the same name as a TPTP statement-level
   keyword (fof, tff, cnf, thf, tcf, include), Sledgehammer exports
   it as a bare symbol name, causing Zipperposition to fail to parse
   the file entirely.

   This is a DIFFERENT bug — it is in Sledgehammer's TPTP export
   rather than in Zipperposition's lambda-free checker. (Although
   Alex Bentkamp confirmed it is actually a Zipperposition parser
   bug — TPTP does not prohibit these as symbol names.)
   ================================================================ *)

lemma parse_bug_fof: "fof = (fof :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma parse_bug_tff: "tff = (tff :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma parse_bug_cnf: "cnf = (cnf :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma parse_bug_thf: "thf = (thf :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

lemma parse_bug_include: "include = (include :: nat)"
  sledgehammer [prover = zipperposition, slices = 1, timeout = 10, overlord]
  oops

end
