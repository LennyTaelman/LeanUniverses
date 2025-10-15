import Mathlib

/-
  # Dependent product types
-/


/-
  ## Formation rule

  Given
    A : Type
    B (a : A) : Type
  can form
    Π (a : A), B a : Type

-/

-- example: take A = ℕ and B (n) = Fin (n + 1) = {0, ..., n}
def B (n : ℕ) : Type := Fin (n + 1)

-- P is the type of all dependent functions that map n to an element of {0, ..., n}
def P : Type := Π (n : ℕ), B n

#check P

/-
  ## Introduction rule (function abstraction)

  Given moreover
    b (x : A) : B x
  can form the `dependent function'
    fun a ↦ b a : Π (a : A), B a
-/

def b (x : ℕ) : B x :=  Fin.ofNat' (x + 1) x
def f : P := fun x ↦ b x

#check f


/-
  ## Elimination rule (function application)

  Given
    g : Π (a : A), B a
    a : A
  can form the term
    g a : B a
-/

variable (g : P) (a : ℕ)

#check g a



/-
  ## Computation rule (applying an abstracted function does the obvious thing)

  Starting from
    b (x : A) : B x
    a : A
  have
    (fun x ↦ b x) a = b a
-/

-- LHS and RHS are terms of type B a
example : B a := b a
example : B a := (fun x ↦ b x) a

-- they agree by definition
example : (fun x ↦ b x) a = b a := by rfl

-- this means that both reduce to the same normal form
#reduce (fun x ↦ b x) a
#reduce b a


/-
  ## Uniqueness rule (abstracting a function application does the obvious thing)

  Starting from
    f : Π (a : A), B a
  have
    f = fun x ↦ b x

-/
-- both sides are terms of type P
example : P := f
example : P := (fun x ↦ f x)

-- they agree by definition
example : (fun x ↦ f x) = f := rfl

-- this means that both reduce to the same normal form
#reduce (fun x ↦ f x)
#reduce f
