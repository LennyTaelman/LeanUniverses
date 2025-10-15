import Mathlib

/-
  # Inductive types 1

  In this file we illustrate this by a simple example.
-/


/-
  ## Formation rule

  We can form
    Two : Type
-/

inductive Two : Type where
  | zero : Two
  | one : Two

#check Two


/-
  Lean  automatically activates introduction, elimination, computation and
  uniqueness rules. We'll see them in action below.
-/



/-
  ## Introduction rules

  We can form
    zero : Two
    one : Two
-/



#check Two.zero
#check Two.one


/-
  ## Elimination rules

  To define a term depending on a variable x of type Two, it suffices to specify
  the cases where x is zero and where x is one.
-/

variable (x : Two)

def a (x : Two) : ℕ :=
  match x with
  | Two.zero => 0
  | Two.one => 1

#check a x


/-
  ## Computation rule

  Specializing such term at zero or one does the obvious thing.
-/

example : a Two.zero = 0 := by rfl
example : a Two.one = 1 := by rfl

#reduce a Two.zero
#reduce a Two.one




/-
  Inductive type in higher universe?
-/

inductive MyNat' : Type 1 where
  | zero : MyNat'
  | succ : MyNat' → MyNat'

inductive MyNat'' : Prop where
  | zero : MyNat''
  | succ : MyNat'' → MyNat''


variable (X0 : Type 0) (X1 : Type 1) (X2 : Type 2)

#check X0 × X1
