import Mathlib
noncomputable section

open Set Function

/-
  In this file we show that the closure of a small dense subset of a Hausdorff
  space is small.

  This is vibe-coded and should be golfed. The file was drafted by Gemini 2.5
  Pro, based on https://stacks.math.columbia.edu/tag/0909. The result had a few
  issues, which were autonomously debugged and corrected by Claude-4.5-Sonnet in
  Cursor agent mode.

  The statements `tricky1` and `tricky2` isolated issues that the coding agent
  could not overcome, and where provided by me. After which Gemini 2.5 Pro in
  combination with Claude-4.5-Sonnet in Cursor agent mode were able to complete
  the proof.
-/



variable {Y : Type 1} [TopologicalSpace Y]

lemma closure_of_open_inter_dense_is_closure_of_open
    {S U : Set Y} (h_dense : Dense S) (hU : IsOpen U) :
    closure (S ∩ closure U) = closure U := by
  have h_subset : closure (S ∩ closure U) ⊆ closure U := by
    conv_rhs => rw [← closure_closure]
    apply closure_mono
    exact inter_subset_right
  refine Subset.antisymm h_subset (fun y hy => ?_)
  rw [mem_closure_iff]
  intro V hV y_mem_V
  have h_intersect : (V ∩ U).Nonempty := by
    rw [mem_closure_iff] at hy
    specialize hy V hV y_mem_V
    exact hy
  have h_open_VU : IsOpen (V ∩ U) := IsOpen.inter hV hU
  have h_dense_intersect : (S ∩ (V ∩ U)).Nonempty := by
    obtain ⟨w, hw⟩ := h_intersect
    have w_in_closure_S : w ∈ closure S := h_dense w
    rw [mem_closure_iff] at w_in_closure_S
    have := w_in_closure_S (V ∩ U) h_open_VU hw
    rw [show (S ∩ (V ∩ U)).Nonempty ↔ (V ∩ U ∩ S).Nonempty by
      simp only [Set.nonempty_iff_ne_empty]
      rw [show S ∩ (V ∩ U) = V ∩ U ∩ S by tauto_set]]
    exact this
  rcases h_dense_intersect with ⟨z, hz⟩
  exact ⟨z, hz.2.1, hz.1, subset_closure hz.2.2⟩

/-- The map from Y to P(P(S)). -/
def theta
    (S : Set Y) (y : Y) : Set (Set S) :=
  { T | ∃ (U : Set Y), IsOpen U ∧ y ∈ closure U ∧ T = {s : S | s.val ∈ closure U} }

lemma theta_is_injective {Y : Type 1} [TopologicalSpace Y] [T2Space Y]
    {S : Set Y} (h_dense : Dense S) :
    Injective (theta S) := by
  -- To prove injectivity, we assume the images are equal for two points y₁ and y₂...
  intros y₁ y₂ h_maps_eq
  -- ...and prove a contradiction if we assume the points are different.
  by_contra h_neq_pts

  -- The T2Space property gives us disjoint open neighborhoods U and V for y₁ and y₂.
  rcases t2_separation h_neq_pts with ⟨U, V, hU, hV, hy₁, hy₂, h_disjoint⟩

  -- Let's define T as the subset of S corresponding to the closure of U.
  let T : Set S := {s : S | s.val ∈ closure U}

  -- By definition, T is in the set for y₁, because y₁ is in U (and U is a subset of its own closure).
  have T_in_y₁ : T ∈ theta S y₁ := by
    use U, hU
    exact ⟨subset_closure hy₁, rfl⟩

  -- Since we assumed the maps produce equal sets, T must also be in the set for y₂.
  have T_in_y₂ : T ∈ theta S y₂ := h_maps_eq ▸ T_in_y₁

  -- Unpacking the definition of `T ∈ injection_map S y₂` gives us some open set W.
  rcases T_in_y₂ with ⟨W, hW, hy₂_closure_W, hT_eq_W⟩

  -- From hT_eq_W, we know `{s | s.val ∈ closure U} = {s | s.val ∈ closure W}`.
  -- This implies the underlying sets in Y are equal when intersected with S.
  have S_inter_eq : S ∩ closure U = S ∩ closure W := by
    ext z
    simp only [mem_inter_iff, and_congr_right_iff]
    exact fun hzS => (Set.ext_iff.mp hT_eq_W) ⟨z, hzS⟩

  -- Now, a key step: since the intersections with S are equal, their closures are equal.
  have closure_inter_eq : closure (S ∩ closure U) = closure (S ∩ closure W) := by
    rw [S_inter_eq]

  -- Using our helper lemma, we can simplify this to `closure U = closure W`.
  rw [closure_of_open_inter_dense_is_closure_of_open h_dense hU] at closure_inter_eq
  rw [closure_of_open_inter_dense_is_closure_of_open h_dense hW] at closure_inter_eq

  -- We know `y₂ ∈ closure W`. Since `closure W = closure U`, it follows that `y₂ ∈ closure U`.
  have hy₂_in_closure_U : y₂ ∈ closure U := by rwa [closure_inter_eq]

  -- Since y₂ ∈ closure U and V is an open neighborhood of y₂, we get V ∩ U ≠ ∅
  have hVU : (V ∩ U).Nonempty := by
    have hc := (mem_closure_iff).1 hy₂_in_closure_U
    exact hc V hV hy₂
  -- But U and V are disjoint, contradiction
  rcases hVU with ⟨z, hzV, hzU⟩
  exact (Set.disjoint_left.mp h_disjoint) hzU hzV


theorem key_smallness [T2Space Y]
      (S : Set Y) [Small.{0} S] (h_dense : Dense S) : Small.{0} Y := by
  exact small_of_injective (theta_is_injective h_dense)


lemma tricky1 (Z : Type 1) (S T : Set Z) (h1 : S ⊆ T) [hS : Small.{0} S] : Small.{0} {x : T | x.val ∈ S} := by
  -- We show that `{x : T | x.val ∈ S}` is equivalent to `S` as a Type.
  let S' := {x : T | x.val ∈ S}
  let equiv_S'_S : S' ≃ S :=
    { toFun    := fun x => ⟨x.val, x.property⟩,
      invFun   := fun s => ⟨⟨s.val, h1 s.property⟩, s.property⟩,
      left_inv := fun x => by simp,
      right_inv:= fun s => by simp }
  exact Iff.mpr (small_congr equiv_S'_S) hS


lemma tricky2 (Z : Type 1) [TopologicalSpace Z] (S : Set Z) : Dense {x : closure S | x.val ∈ S} := by
  classical
  -- Let S' denote S viewed as a subset of closure S
  set S' : Set (closure S) := {x | x.val ∈ S}
  -- characterization of density by neighborhoods in the subspace
  refine (dense_iff_inter_open.2 ?_)
  intro U hU_open hU_nonempty
  -- U open in closure S, so it is the preimage of some V open in Z
  rcases isOpen_induced_iff.mp hU_open with ⟨V, hV_open, rfl⟩
  -- pick a point x in U
  rcases hU_nonempty with ⟨x, hxU⟩
  have hxV : x.val ∈ V := by
    simp only [mem_preimage] at hxU
    exact hxU
  -- use closure characterization for x.val ∈ closure S
  have : (V ∩ S).Nonempty :=
    (mem_closure_iff.mp x.property) V hV_open hxV
  rcases this with ⟨y, hyV, hyS⟩
  -- build a point in U ∩ S'
  use ⟨y, subset_closure hyS⟩
  constructor
  · -- in U = Subtype.val ⁻¹' V
    show y ∈ V
    exact hyV
  · -- in S'
    simpa [S', mem_setOf_eq]

/-- The closure of a small subset of a T2 space is small. -/

theorem small_closure [T2Space Y] (S : Set Y) [hS : Small.{0} S] : Small.{0} (closure S) := by
  -- We view `S` as a subset `S'` of the space `closure S`.
  let S' : Set (closure S) := {x | x.val ∈ S}
  have h_dense_S' : Dense S' := tricky2 Y S
  letI : Small.{0} S' := tricky1 Y S (closure S) subset_closure
  exact key_smallness S' h_dense_S'
