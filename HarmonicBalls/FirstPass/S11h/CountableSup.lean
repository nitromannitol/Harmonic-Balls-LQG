import Mathlib

/-! # Countable reduction of pair suprema (fp-S11h, owner n2)

FIRST-PASS NEW, general measure theory and topology (no pinch-specific content). Used for the measurability of the
pinch events `Ẽ₁, Ẽ₂, Ẽ₃` as functions of the field (paper line 3630: "each event is measurable with respect to the
field in `B_7`"): a supremum over pairs `x, y ∈ A` of a function continuous on `A × A` equals the supremum over a
countable subset `t ⊆ A` depending only on `A`. Then the supremum is almost everywhere measurable in `ω`.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- For every `A ⊆ ℂ` there is a countable `t ⊆ A`, depending only on `A`, such that for every `F : ℂ → ℂ → ℝ≥0∞`
continuous on `A × A`, the supremum over pairs in `A` equals the supremum over pairs in `t`. -/
theorem exists_countable_iSup_pair_eq (A : Set ℂ) :
    ∃ t : Set ℂ, t.Countable ∧ t ⊆ A ∧ ∀ F : ℂ → ℂ → ℝ≥0∞,
      ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (A ×ˢ A) →
      (⨆ x ∈ A, ⨆ y ∈ A, F x y) = ⨆ x ∈ t, ⨆ y ∈ t, F x y := by
  obtain ⟨t, htc, htA, hAt⟩ := TopologicalSpace.exists_countable_dense_subset A
  refine ⟨t, htc, htA, fun F hF => le_antisymm ?_ ?_⟩
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨c, hRc, hcF⟩ := exists_between hlt
    have hev : ∀ᶠ p in 𝓝[A ×ˢ A] (x, y), c < F p.1 p.2 :=
      (hF (x, y) ⟨hx, hy⟩).eventually (lt_mem_nhds hcF)
    have hxy : (x, y) ∈ closure (t ×ˢ t) := by
      rw [closure_prod_eq]
      exact ⟨hAt hx, hAt hy⟩
    have hne : (𝓝[t ×ˢ t] (x, y)).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hxy
    have hev' : ∀ᶠ p in 𝓝[t ×ˢ t] (x, y), c < F p.1 p.2 :=
      Filter.Eventually.filter_mono (nhdsWithin_mono (x, y) (prod_mono htA htA)) hev
    obtain ⟨p, hcp, hpt⟩ := (hev'.and self_mem_nhdsWithin).exists
    have h1 : F p.1 p.2 ≤ ⨆ x ∈ t, ⨆ y ∈ t, F x y :=
      le_iSup₂_of_le p.1 hpt.1 (le_iSup₂_of_le p.2 hpt.2 le_rfl)
    have hcR : c < ⨆ x ∈ t, ⨆ y ∈ t, F x y := hcp.trans_le h1
    exact lt_asymm hRc hcR
  · refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    exact le_iSup₂_of_le x (htA hx) (le_iSup₂_of_le y (htA hy) le_rfl)

/-- Almost everywhere measurability of a pair supremum over `A`, when each value is a.e. measurable and the function
is a.s. continuous on `A × A`. -/
theorem aemeasurable_iSup_pair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (A : Set ℂ)
    (F : Ω → ℂ → ℂ → ℝ≥0∞) (hmeas : ∀ x y, AEMeasurable (fun ω => F ω x y) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℂ × ℂ => F ω p.1 p.2) (A ×ˢ A)) :
    AEMeasurable (fun ω => ⨆ x ∈ A, ⨆ y ∈ A, F ω x y) P := by
  obtain ⟨t, htc, -, hsup⟩ := exists_countable_iSup_pair_eq A
  have : Countable t := htc.to_subtype
  have hEq : (fun ω => ⨆ x ∈ t, ⨆ y ∈ t, F ω x y) =ᵐ[P] fun ω => ⨆ x ∈ A, ⨆ y ∈ A, F ω x y := by
    filter_upwards [hcont] with ω hω
    exact (hsup (F ω) hω).symm
  have key : (fun ω => ⨆ x ∈ t, ⨆ y ∈ t, F ω x y) = fun ω => ⨆ x : t, ⨆ y : t, F ω (x : ℂ) (y : ℂ) := by
    funext ω
    apply le_antisymm
    · exact iSup₂_le fun x hx => iSup₂_le fun y hy =>
        le_iSup_of_le ⟨x, hx⟩ (le_iSup_of_le ⟨y, hy⟩ le_rfl)
    · exact iSup_le fun x => iSup_le fun y => le_iSup₂_of_le (x : ℂ) x.2 (le_iSup₂_of_le (y : ℂ) y.2 le_rfl)
  have hm : AEMeasurable (fun ω => ⨆ x : t, ⨆ y : t, F ω (x : ℂ) (y : ℂ)) P :=
    AEMeasurable.iSup fun x => AEMeasurable.iSup fun y => hmeas (x : ℂ) (y : ℂ)
  refine AEMeasurable.congr ?_ hEq
  rw [key]
  exact hm

end HarmonicBalls
