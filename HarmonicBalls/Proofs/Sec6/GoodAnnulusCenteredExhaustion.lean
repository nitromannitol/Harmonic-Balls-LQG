import HarmonicBalls.Proofs.Sec6.GoodAnnulusModConstLocality
import HarmonicBalls.Proofs.Sec8.VagueMassConvergence
import HarmonicBalls.Proofs.Sec8.RandomMeasureContinuitySets

/-! # Good-annulus locality from centered approximations -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal Topology

/-- Centered circle-average versions on an exhaustion of the annulus imply
locality of its good-annulus event when the exhaustion sets and their union
are almost surely continuity sets for the LQG measure. The local field
may be a recentered version of the field defining the measure. -/
theorem isFieldMeasurableModConst_goodAnnulus_of_centered_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {hC hLocal : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (U : Set ℂ) (hm : fieldSigmaAlgebraModConst 0 hLocal U ≤ mΩ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hbounded : Bornology.IsBounded (⋃ n, E n))
    (hE : (⋃ n, E n) = annulus z (3 * r) (5 * r))
    (hfront : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0)
    (z₀ : ℂ) (d : ℕ → Ω → ℂ → ℝ)
    (hdm : ∀ n, @Measurable (Ω × ℂ) ℝ
      ((fieldSigmaAlgebraModConst 0 hLocal U).prod inferInstance) _
      (Function.uncurry (d n)))
    (hdeq : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ E n,
      d n ω w = fieldCircleAverage 0 (hcirc ω) (dyadicScale n) w -
        fieldCircleAverage 0 (hcirc ω) (dyadicScale n) z₀) :
    IsFieldMeasurableModConst P 0 hLocal U {ω | IsGoodAnnulus (μ ω) r z a b} := by
  let := hgff.isProbabilityMeasure
  obtain ⟨S, hcount, hpi, _, hopen, hgen, hSfront⟩ :=
    hgff.exists_ae_lqg_continuity_piSystem P hμ
  have hfronts := ae_frontiers_intersections_of_common_continuity P μ E S hfront hSfront
  apply isFieldMeasurableModConst_goodAnnulus_of_mass_ratio_versions P hLocal U μ hm
    (hgff.aemeasurable_lqgMeasure hμ) hr z ha b hatom hfinite hpositive hpolar
    S hcount hgen hpi (fun V hV => (hopen V hV).measurableSet)
  intro V hV
  have hpos : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞ := by
    filter_upwards [hpositive, hfinite] with ω hp hf
    rw [hE]
    exact ⟨hp.ne', hf⟩
  have hfV : ∀ᵐ ω ∂P,
      (∀ n, μ ω (frontier (E n)) = 0 ∧ μ ω (frontier (V ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (V ∩ ⋃ n, E n)) = 0 := by
    filter_upwards [hfronts] with ω hω
    exact hω V hV
  have hv := exists_local_lqg_ratio_version_of_centered_exhaustion P
    (fieldSigmaAlgebraModConst 0 hLocal U) hgff hμ E hEm hmono hbounded V
    (hopen V hV).measurableSet hfV hpos z₀ d hdm hdeq
  simpa only [hE] using hv

end HarmonicBalls.Section6
