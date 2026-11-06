import HarmonicBalls.Proofs.Sec6.SingularMiddleAnnulusSmallTolerance
import HarmonicBalls.Proofs.Sec6.SingularMassTypicalDyadicAnnuli

/-! # Simultaneous dyadic singular annulus counts

The count uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
universe u

/-- One mass threshold works almost surely at every centre of the middle
annulus and every scale in a prescribed countable family, eventually in
dyadic windows. The index from which the estimate holds may depend on the
field and the physical scale, but not on the centre. -/
theorem exists_ae_all_middleAnnulus_singular_goodAnnuli_count
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ 0 hcirc μ₀)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {b : ℝ} (hb : 0 < b) (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1)
    (s : ℕ → ℝ) (hs : ∀ i, 0 < s i) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ᵐ ω ∂P, ∀ i, ∀ᶠ n : ℕ in atTop,
      ∀ w ∈ annulus (0 : ℂ) (1/2) 1,
        (β / 16) * Real.logb 7 ((dyadicScale n) ^ (-1 : ℝ)) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n) ((dyadicScale n) ^ (3 / 4 : ℝ)) ∧
          (∃ k : ℕ, r = (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) (s i * r) w
            ((a/8) / ((1001 : ℝ) ^ |-(γ*α)|) ^ 2) b}.ncard : ℝ) := by
  obtain ⟨a, ha, hcount⟩ := exists_all_middleAnnulus_singular_goodAnnulus_counts_smallTolerance
    hgrowth h hμ hμ₀ hAff hCC hγ hγ2 hα hb β hβ
  refine ⟨a, ha, ae_all_iff.mpr ?_⟩
  intro i
  simpa only [dyadicScale, mem_ofPred_eq] using (hcount (s i) (hs i)).ae_eventually_dyadic

end HarmonicBalls.Section6
