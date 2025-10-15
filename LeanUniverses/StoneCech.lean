import Mathlib
import LeanUniverses.SmallClosure

noncomputable section

/-
  Let X be a topological space. In this file we construct its Stone-Cech compactification.
-/
variable (X : Type 0) [TopologicalSpace X]


/-
  Consider the type I of all pairs (Y, f: X → Y) where Y is a compact
  Hausdorff space and f is a continuous function.
-/
structure I : Type 1 where
  Y : Type 0
  f : X → Y
  top : TopologicalSpace Y
  is_compact : CompactSpace Y
  is_hausdorff : T2Space Y
  is_continuous : Continuous f

attribute [instance] I.top
attribute [instance] I.is_compact
attribute [instance] I.is_hausdorff
attribute [instance] I.is_continuous

/-
  Consider the product of all the Y's and equip it with the product topology.
  Show that it is compact and Hausdorff.
-/
def BigProduct : Type 1 := Π (i : I X), i.Y
instance : TopologicalSpace (BigProduct X) := Pi.topologicalSpace
instance : CompactSpace (BigProduct X) := Pi.compactSpace
instance : T2Space (BigProduct X) := Pi.t2Space

/-
  Define the canonical map from X to BigProduct, and verify that it is continuous
-/
def canonicalMap (x : X) : BigProduct X := fun i => i.f x

instance : Continuous (canonicalMap X) := by
  apply continuous_pi
  intro i
  exact i.is_continuous


/-
  Define StoneCechCompactification as the closure of the image of the canonical
  map. Equip it with the subspace topology
-/
def SC1 : Type 1 := closure (Set.range (canonicalMap X))

instance : TopologicalSpace (SC1 X) := instTopologicalSpaceSubtype
instance : CompactSpace (SC1 X) := isCompact_iff_compactSpace.mp (IsClosed.isCompact isClosed_closure)
instance : T2Space (SC1 X) := inferInstanceAs (T2Space (closure (Set.range (canonicalMap X))))


/-
  Now we should show that SC1 is actually a small type (lives in Type 0). The
  key argument is to show that SC1 is not bigger than the power set of the power set of
  X (which is small!).

  This concentrates the 'set-theoretic' issue into one place. The main result
  below is `SC1_is_small : Small.{0} (SC1 X)`. The main argument is outsourced
  to `small_closure` in `SmallClosure.lean`, which shows that the closure of a
  small subset of a Hausdorff space is again small.
-/



theorem SC1_is_small : Small.{0} (SC1 X) := by
  exact small_closure (Set.range (canonicalMap X))

instance : Small.{0} (SC1 X) := SC1_is_small X
def SC0 : Type 0 := Shrink.{0} (SC1 X)
def equivSC0_SC1 : SC0 X ≃ SC1 X := (equivShrink (SC1 X)).symm


/-
  SC0 inherits topology from SC1 via the equivalence SC0 ≃ SC1. It is compact
  and Hausdorff since SC1 is.
-/
instance : TopologicalSpace (SC0 X) := TopologicalSpace.induced (equivSC0_SC1 X) inferInstance
def homeoSC0_SC1 : SC0 X ≃ₜ SC1 X := Equiv.toHomeomorphOfIsInducing (equivSC0_SC1 X) { eq_induced := rfl }
instance : CompactSpace (SC0 X) := (homeoSC0_SC1 X).symm.compactSpace
instance : T2Space (SC0 X) := (homeoSC0_SC1 X).symm.t2Space

/-
  Construct the map from X to SC0, and verify that it is continuous
-/
def mapSC0 (x : X) : SC0 X := (equivSC0_SC1 X).symm ⟨canonicalMap X x, subset_closure (Set.mem_range_self x)⟩
instance : Continuous (mapSC0 X) := by
  apply Continuous.comp (homeoSC0_SC1 X).symm.continuous
  exact Continuous.subtype_mk (continuous_pi (fun i ↦ i.is_continuous)) _
