import HarmonicBalls.Proofs.Sec6.JointCollarNearbyCounts

/-! # Common good-annulus radii at nearby centres

The imported grid estimate uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- A good-annulus and collar count transfers at the same radii: each
counted radius is good at both the original and the nearby centre. -/
theorem jointCollar_count_le_common_goodAnnulus_count
    {η : ℝ} (hη : 0 < η) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure ℂ) (s t : ℝ), 0 < s → 0 < t →
      ∀ z w : ℂ, dist w z < δ * (s*t) → ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      (∀ r : ℝ, t ≤ r → 0 < μ (annulus z (3*(s*r)) (5*(s*r)))) →
      (∀ r : ℝ, t ≤ r → μ (annulus z (3*(s*r)) (5*(s*r))) ≠ ∞) →
      ENNReal.ofReal b + 2 * e + e ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      ∀ T : Set ℝ, T.Finite → (∀ r ∈ T, t ≤ r) →
      ({r : ℝ | r ∈ T ∧ IsGoodAnnulus μ (s*r) z a b ∧
        μ (annulus z (3*(s*r)-η*(s*r)) (5*(s*r)+η*(s*r)) \
          annulus z (3*(s*r)+η*(s*r)) (5*(s*r)-η*(s*r))) ≤
          d * μ (annulus z (3*(s*r)) (5*(s*r)))}).ncard ≤
      ({r : ℝ | r ∈ T ∧ IsGoodAnnulus μ (s*r) z a b ∧
        IsGoodAnnulus μ (s*r) w a' b'}).ncard := by
  obtain ⟨δ, hδ, ht⟩ := jointCollar_count_le_nearby_goodAnnulus_count hη he
  refine ⟨δ, hδ, ?_⟩
  intro μ s t hs htpos z w hw a a' amid b b' d hpos hfin hbudget hmid hslack T hT hlo
  let U : Set ℝ := {r | r ∈ T ∧ IsGoodAnnulus μ (s*r) z a b}
  have hU : U.Finite := hT.subset (fun _ hr => hr.1)
  have hUlo : ∀ r ∈ U, t ≤ r := fun r hr => hlo r hr.1
  have hcount := ht μ s t hs htpos z w hw a a' amid b b' d hpos hfin
    hbudget hmid hslack U hU hUlo
  simp only [U, Set.mem_ofPred_eq] at hcount
  convert hcount using 1 <;> congr 1 <;> ext r <;> simp only [Set.mem_ofPred_eq] <;> tauto

end HarmonicBalls.Section6
