import Mathlib

#check Nat
#check Int


/-
  Basics universes:
   Prop and Type ("statements and sets")
-/

example : Prop := 1 + 1 = 2
example : Prop := 1 + 1 = 3

example : Type := Unit -- the singleton type
example : Type := ℕ
example : Type := ℝ
example : Type := Set ℝ -- the power set of ℝ

example : Type 1 := Type -- the type of types

example : Type 1 := Set Type -- the type of sets of Types
example : Type 1 := ℝ → Type -- the type of families of types indexed by ℝ





/-
  Three fundamental type-theoretic constructions:
    products (including function types)
    quotients
    inductive types (including coproducts?)
-/


-- the product of a u-type's worth of v-type's is a (max u v)-type
universe u v
variable (I : Type u) (X : I → Type v)
example : Type (max u v) := Π i : I, X i


-- the product of a u-type's worth of props is a prop
variable (I : Type u) (P : I → Prop)
example : Prop := ∀ i : I, P i
example : Prop := Π i : I, P i


-- the quotient of a u-type by a relation is a u-type
variable (X : Type u) (r : X → X → Prop)
example : Type u := Quot r

-- an inductive type with a constructor indexed by a u-type and a v-type
-- is a (max u v)-type
variable (X : Type u) (Y : Type v)
inductive sum_type where
  | intro_X : X → sum_type
  | intro_Y : Y → sum_type

#check sum_type
