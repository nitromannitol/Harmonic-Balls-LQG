import Mathlib

/-! # Countable reduction of pair suprema

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

/-- Countable reduction of an infimum (general, no pinch content): if `t ⊆ P` is dense in `P` (`P ⊆ closure t`) and `G` is
continuous on `P`, then `⨅ p ∈ P, G p = ⨅ p ∈ t, G p`. Used for the distance `ofReal (setDist D S₁ S₂)` between two compact
sets, see `FirstPass/S11h/ThirdEventMeasurable.lean`. -/
theorem iInf_eq_countable_of_continuousOn {X : Type*} [TopologicalSpace X] (P t : Set X) (htP : t ⊆ P)
    (hPt : P ⊆ closure t) (G : X → ℝ≥0∞) (hG : ContinuousOn G P) :
    (⨅ p ∈ P, G p) = ⨅ p ∈ t, G p := by
  refine le_antisymm ?_ ?_
  · exact le_iInf₂ fun p hp => iInf₂_le p (htP hp)
  · refine le_iInf₂ fun p hp => ?_
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨c, hGc, hcR⟩ := exists_between hlt
    have hev : ∀ᶠ q in 𝓝[P] p, G q < c := (hG p hp).eventually (gt_mem_nhds hGc)
    have hne : (𝓝[t] p).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hPt hp)
    have hev' : ∀ᶠ q in 𝓝[t] p, G q < c :=
      Filter.Eventually.filter_mono (nhdsWithin_mono p htP) hev
    obtain ⟨q, hqc, hqt⟩ := (hev'.and self_mem_nhdsWithin).exists
    have h1 : (⨅ p' ∈ t, G p') ≤ G q := iInf₂_le q hqt
    exact lt_irrefl c ((hcR.trans_le h1).trans hqc)

/-- Almost everywhere measurability of an infimum over a set `S` of a family which is a.s. continuous on `S` (general):
the countable set `t ⊆ S` depends only on `S`, and the infimum over `S` equals the infimum over `t` almost surely. -/
theorem aemeasurable_iInf_countable {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X]
    [SecondCountableTopology X] (P : Measure Ω) (S : Set X) (G : Ω → X → ℝ≥0∞)
    (hmeas : ∀ p, AEMeasurable (fun ω => G ω p) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p => G ω p) S) :
    AEMeasurable (fun ω => ⨅ p ∈ S, G ω p) P := by
  obtain ⟨t, htc, htS, hSt⟩ := TopologicalSpace.exists_countable_dense_subset S
  have : Countable t := htc.to_subtype
  have hEq : (fun ω => ⨅ p ∈ t, G ω p) =ᵐ[P] fun ω => ⨅ p ∈ S, G ω p := by
    filter_upwards [hcont] with ω hω
    exact (iInf_eq_countable_of_continuousOn S t htS hSt (G ω) hω).symm
  have key : (fun ω => ⨅ p ∈ t, G ω p) = fun ω => ⨅ p : t, G ω (p : X) := by
    funext ω
    exact le_antisymm (le_iInf fun p : t => iInf₂_le (p : X) p.2)
      (le_iInf₂ fun (p : X) (hp : p ∈ t) => iInf_le (fun q : t => G ω (q : X)) ⟨p, hp⟩)
  have hm : AEMeasurable (fun ω => ⨅ p : t, G ω (p : X)) P :=
    AEMeasurable.iInf fun p => hmeas (p : X)
  refine AEMeasurable.congr ?_ hEq
  rw [key]
  exact hm

end HarmonicBalls
