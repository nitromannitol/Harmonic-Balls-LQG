import HarmonicBalls.Proofs.Sec9.MassEntryTimeUniqueness

/-! # Comparison of nested mass families

When two mass-parametrized families are pointwise nested, their common
entry-time representative controls comparisons at every pair of distinct
masses outside a single spatial null set.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- Equal left rational envelopes of two nested families give both strict
cross-family inclusions at each point. -/
theorem nested_mass_families_cross_of_eq_envelopes
    (A B : ℝ → Set ℂ) (x : ℂ)
    (hA : ∀ s t : ℝ, 0 < s → s ≤ t → A s ⊆ A t)
    (hB : ∀ s t : ℝ, 0 < s → s ≤ t → B s ⊆ B t)
    (heq : ∀ t : ℝ, 0 < t →
      (x ∈ leftRationalMassEnvelope A t ↔ x ∈ leftRationalMassEnvelope B t)) :
    ∀ s t : ℝ, 0 < s → s < t →
      (x ∈ A s → x ∈ B t) ∧ (x ∈ B s → x ∈ A t) := by
  intro s t hs hst
  obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hst
  have hq : 0 < (q : ℝ) := hs.trans hsq
  have hAt : x ∈ leftRationalMassEnvelope A t → x ∈ B t := by
    intro hx
    have hx' := (heq t (hs.trans hst)).mp hx
    simp only [leftRationalMassEnvelope, mem_iUnion] at hx'
    obtain ⟨p, hp, hpt, hxp⟩ := hx'
    exact hB p t hp hpt.le hxp
  constructor
  · intro hx
    apply hAt
    simp only [leftRationalMassEnvelope, mem_iUnion]
    exact ⟨q, hq, hqt, hA s q hs hsq.le hx⟩
  · intro hx
    have hx' : x ∈ leftRationalMassEnvelope B t := by
      simp only [leftRationalMassEnvelope, mem_iUnion]
      exact ⟨q, hq, hqt, hB s q hs hsq.le hx⟩
    have hx'' := (heq t (hs.trans hst)).mpr hx'
    simp only [leftRationalMassEnvelope, mem_iUnion] at hx''
    obtain ⟨p, hp, hpt, hxp⟩ := hx''
    exact hA p t hp hpt.le hxp

/-- At a fixed point, two nested families with equal left rational envelopes
can disagree at at most one positive mass. -/
theorem nested_mass_families_disagree_at_most_once
    (A B : ℝ → Set ℂ) (x : ℂ)
    (hA : ∀ s t : ℝ, 0 < s → s ≤ t → A s ⊆ A t)
    (hB : ∀ s t : ℝ, 0 < s → s ≤ t → B s ⊆ B t)
    (heq : ∀ t : ℝ, 0 < t →
      (x ∈ leftRationalMassEnvelope A t ↔ x ∈ leftRationalMassEnvelope B t)) :
    ∀ s t : ℝ, 0 < s → 0 < t →
      ¬ (x ∈ A s ↔ x ∈ B s) → ¬ (x ∈ A t ↔ x ∈ B t) → s = t := by
  have hcross := nested_mass_families_cross_of_eq_envelopes A B x hA hB heq
  have hlater : ∀ s t : ℝ, 0 < s → s < t →
      ¬ (x ∈ A s ↔ x ∈ B s) → (x ∈ A t ↔ x ∈ B t) := by
    intro s t hs hst hne
    by_cases ha : x ∈ A s
    · have hat := hA s t hs hst.le ha
      have hbt := (hcross s t hs hst).1 ha
      exact ⟨fun _ => hbt, fun _ => hat⟩
    · have hb : x ∈ B s := by
        by_contra hb
        exact hne ⟨fun h => (ha h).elim, fun h => (hb h).elim⟩
      have hat := (hcross s t hs hst).2 hb
      have hbt := hB s t hs hst.le hb
      exact ⟨fun _ => hbt, fun _ => hat⟩
  intro s t hs ht hsn htn
  rcases lt_trichotomy s t with h | h | h
  · exact (htn (hlater s t hs h hsn)).elim
  · exact h
  · exact (hsn (hlater t s ht h htn)).elim

universe u

/-- On one probability-one event, any two nested same-centre bounded
subharmonic-ball families satisfy strict cross-mass inclusion at almost every
point, simultaneously for all positive masses. At such a point the families
can disagree at at most one mass. The exceptional spatial null set can depend
on the pair of families. -/
theorem ae_nested_massParametrized_subharmonicBall_comparison
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : ℝ → Set ℂ) (z : ℂ),
      (∀ t : ℝ, 0 < t → Bornology.IsBounded (A t) ∧
        IsSubharmonicBall (μ ω) (A t) z ∧ μ ω (A t) = ENNReal.ofReal t) →
      (∀ t : ℝ, 0 < t → Bornology.IsBounded (B t) ∧
        IsSubharmonicBall (μ ω) (B t) z ∧ μ ω (B t) = ENNReal.ofReal t) →
      (∀ s t : ℝ, 0 < s → s ≤ t → A s ⊆ A t) →
      (∀ s t : ℝ, 0 < s → s ≤ t → B s ⊆ B t) →
      ∀ᵐ x ∂(μ ω),
        (∀ s t : ℝ, 0 < s → s < t →
          (x ∈ A s → x ∈ B t) ∧ (x ∈ B s → x ∈ A t)) ∧
        (∀ s t : ℝ, 0 < s → 0 < t → ¬ (x ∈ A s ↔ x ∈ B s) →
          ¬ (x ∈ A t ↔ x ∈ B t) → s = t) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_massParametrized_subharmonicBall_entry_time_unique hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro A B z hA hB hmonoA hmonoB
  filter_upwards [hω A B z hA hB] with x hx
  exact ⟨nested_mass_families_cross_of_eq_envelopes A B x hmonoA hmonoB hx.2,
    nested_mass_families_disagree_at_most_once A B x hmonoA hmonoB hx.2⟩

end HarmonicBalls
