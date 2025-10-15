import Mathlib

/-
  # Inductive types 2

  More interesting example: natural numbers.
-/


/-
  ## Formation rule

  We can form
    MyNat : Type
-/

inductive MyNat : Type where
  | zero : MyNat
  | succ : MyNat → MyNat

#check MyNat


/-
  Lean  automatically activates introduction, elimination, computation and
  uniqueness rules. We'll see them in action below.
-/



/-
  ## Introduction rules

  We can form
    zero : MyNat
  And given n : MyNat we can form
    succ n : MyNat
-/


#check MyNat.zero

variable (n : MyNat)

#check MyNat.succ n


/-
  ## Elimination rules

  To define a term depending on a variable x of type MyNat, it suffices to specify
  * the case where x is zero
  * the case where x is succ y, depending on some variable y : MyNat
  This is the principle of induction!
-/

variable (x : MyNat)

def a (x : MyNat) : ℕ :=
  match x with
  | MyNat.zero => 0
  | MyNat.succ y => a y + 2

#check a x
#reduce a MyNat.zero
#reduce a (MyNat.succ MyNat.zero)
#reduce a (MyNat.succ (MyNat.succ MyNat.zero))
