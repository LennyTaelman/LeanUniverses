import Mathlib

/-
  # Inductive types 2

  Another simple example: the type of pairs of natural numbers.
-/


/-
  ## Formation rule
-/

inductive P : Type where
  | mk : ℕ → ℕ → P

#check P



/-
  ## Introduction rules
-/

#check P.mk 3 5



/-
  ## Elimination rules
-/

def a (x : P) : ℕ :=
  match x with
  | P.mk x y => x + y

#check a




/-
  ## Computation rule

  Specializing such term at zero or one does the obvious thing.
-/

example : a (P.mk 3 5) = 3 + 5 := by rfl
