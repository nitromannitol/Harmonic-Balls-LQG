import HarmonicBalls.Proofs.Sec6.ScaleUniformRelativeCollar

/-! # Good-annulus counts with exceptional collars

A finite-scale count can lose at most the number of failed relative-collar
estimates. No assertion about the probability or frequency of failures is made.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

open Classical in
/-- For any finite family of scales, a uniformly nearby centre inherits all
root good annuli except possibly those whose relative collar bound fails. -/
theorem exists_scale_uniform_goodAnnulus_count_le
    {η : ℝ} (hη : 0 < η) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure ℂ) (r : ℕ → ℝ) (s : Finset ℕ)
      (z w : ℂ), (∀ i ∈ s, 0 < r i) →
      (∀ i ∈ s, dist w z < δ * r i) →
      ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      (∀ i ∈ s, 0 < μ (annulus z (3*r i) (5*r i))) →
      (∀ i ∈ s, μ (annulus z (3*r i) (5*r i)) ≠ ∞) →
      ENNReal.ofReal b + 2 * ε + ε ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      (s.filter fun i => IsGoodAnnulus μ (r i) z a b).card ≤
      (s.filter fun i => IsGoodAnnulus μ (r i) w a' b').card +
      (s.filter fun i => d * μ (annulus z (3*r i) (5*r i)) <
        μ (annulus z (3*r i-η*r i) (5*r i+η*r i) \
          annulus z (3*r i+η*r i) (5*r i-η*r i))).card := by
  classical
  obtain ⟨δ, hδ, ht⟩ := exists_scale_uniform_goodAnnulus_of_relative_collar hη hε
  refine ⟨δ, hδ, ?_⟩
  intro μ r s z w hr hw a a' amid b b' d hpos hfin hbudget hmid hslack
  let G := s.filter fun i => IsGoodAnnulus μ (r i) z a b
  let H := s.filter fun i => IsGoodAnnulus μ (r i) w a' b'
  let B := s.filter fun i => d * μ (annulus z (3*r i) (5*r i)) <
    μ (annulus z (3*r i-η*r i) (5*r i+η*r i) \
      annulus z (3*r i+η*r i) (5*r i-η*r i))
  have hsub : G \ B ⊆ H := by
    intro i hi
    have hiG := (Finset.mem_sdiff.mp hi).1
    have hiB := (Finset.mem_sdiff.mp hi).2
    have his := (Finset.mem_filter.mp hiG).1
    have hig := (Finset.mem_filter.mp hiG).2
    have hcollar : μ (annulus z (3*r i-η*r i) (5*r i+η*r i) \
      annulus z (3*r i+η*r i) (5*r i-η*r i)) ≤
        d * μ (annulus z (3*r i) (5*r i)) := by
      apply le_of_not_gt
      intro hb
      exact hiB (Finset.mem_filter.mpr ⟨his, hb⟩)
    exact Finset.mem_filter.mpr ⟨his,
      ht μ (r i) (hr i his) z w (hw i his) a a' amid b b' d
        (hpos i his) (hfin i his) hig hbudget hmid hslack hcollar⟩
  calc
    G.card ≤ (G \ B).card + B.card := Finset.card_le_card_sdiff_add_card
    _ ≤ H.card + B.card := Nat.add_le_add_right (Finset.card_le_card hsub) _

end HarmonicBalls.Section6
