import HarmonicBalls.Proofs.Sec8.RandomGoodAnnulus
import HarmonicBalls.Proofs.Sec8.GoodAnnulusLocality
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureScaling
import HarmonicBalls.Proofs.Sec8.LocalMeasureRatios
import HarmonicBalls.Proofs.Sec8.AEPiSystemRatioRepresentatives
import HarmonicBalls.Draft.Section6

/-! # Good-annulus locality from a normalized local measure -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal

/-- A measurable local measure version, equal almost surely to a finite positive
multiple of the restriction, represents the good-annulus event in the local
modulo-constant field sigma-algebra. -/
theorem isFieldMeasurableModConst_goodAnnulus_of_normalized_restriction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (μ ν : Ω → Measure ℂ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hν : @Measurable Ω (Measure ℂ) (fieldSigmaAlgebraModConst 0 hC U) _ ν)
    (hversion : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      ν ω = c • (μ ω).restrict (annulus z (3 * r) (5 * r)))
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IsFieldMeasurableModConst P 0 hC U {ω | IsGoodAnnulus (μ ω) r z a b} := by
  classical
  let A := annulus z (3 * r) (5 * r)
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  obtain ⟨G, hG, hrep⟩ := exists_measurable_isGoodAnnulus_on_atomless r hr z a b
    (annulus_smallBallHitting_of_ae_point_avoidance r hr z hpolar)
  refine ⟨ν ⁻¹' G, hν hG, ?_⟩
  filter_upwards [hversion, hatom, hfinite, hpositive] with ω hver hatomω hfiniteω hpositiveω
  obtain ⟨c, hc, hct, hνeq⟩ := hver
  change IsGoodAnnulus (μ ω) r z a b = (ν ω ∈ G)
  rw [hνeq]
  have hnull : NullSingletonClass (c • (μ ω).restrict A) := by
    constructor
    intro x
    rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
    have : (μ ω) ({x} ∩ A) = 0 := measure_mono_null inter_subset_left (hatomω x)
    simp [this]
  have hmass : (c • (μ ω).restrict A) A = c * μ ω A := by
    rw [Measure.smul_apply, Measure.restrict_apply hA, inter_self]
    rfl
  have hne : (c • (μ ω).restrict A) A ≠ ∞ := by
    rw [hmass]
    exact ENNReal.mul_ne_top hct hfiniteω
  have hpos : 0 < ENNReal.ofReal a * (c • (μ ω).restrict A) A := by
    rw [hmass]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne'
      (ENNReal.mul_pos hc hpositiveω.ne').ne'
  have hequiv := hrep (c • (μ ω).restrict A) hnull hne hpos
  have hscale := isGoodAnnulus_smul ((μ ω).restrict A) r z a b hc hct
  have hrestrict := isGoodAnnulus_restrict (μ ω) r z a b A (subset_refl _)
  exact propext (hequiv.trans (hscale.trans hrestrict)).symm

/-- A local measurable version of the normalized annular restriction suffices
for modulo-constant locality of the good-annulus event. -/
theorem isFieldMeasurableModConst_goodAnnulus_of_normalized_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (μ : Ω → Measure ℂ)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hversion : ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (fieldSigmaAlgebraModConst 0 hC U) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (annulus z (3 * r) (5 * r)))
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IsFieldMeasurableModConst P 0 hC U {ω | IsGoodAnnulus (μ ω) r z a b} := by
  obtain ⟨ν, hν, hνeq⟩ := hversion
  apply isFieldMeasurableModConst_goodAnnulus_of_normalized_restriction
    P hC U μ ν hr z ha b hν ?_ hatom hfinite hpositive hpolar
  filter_upwards [hνeq, hfinite, hpositive] with ω heq hf hp
  refine ⟨(μ ω (annulus z (3 * r) (5 * r)))⁻¹,
    ENNReal.inv_ne_zero.mpr hf, ENNReal.inv_ne_top.mpr hp.ne', ?_⟩
  exact heq

/-- Countably many local normalized mass-ratio versions determine the local
measure version, and hence the good-annulus event. -/
theorem isFieldMeasurableModConst_goodAnnulus_of_mass_ratio_versions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (μ : Ω → Measure ℂ)
    (hm : fieldSigmaAlgebraModConst 0 hC U ≤ mΩ) (hμ : AEMeasurable μ P)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (S : Set (Set ℂ)) (hcount : S.Countable)
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V)
    (hversion : ∀ V ∈ S, ∃ Y : Ω → ℝ≥0∞,
      @Measurable Ω ℝ≥0∞ (fieldSigmaAlgebraModConst 0 hC U) _ Y ∧
      (fun ω => μ ω (V ∩ annulus z (3 * r) (5 * r)) /
        μ ω (annulus z (3 * r) (5 * r))) =ᵐ[P] Y) :
    IsFieldMeasurableModConst P 0 hC U {ω | IsGoodAnnulus (μ ω) r z a b} := by
  apply isFieldMeasurableModConst_goodAnnulus_of_normalized_version
    P hC U μ hr z ha b ?_ hatom hfinite hpositive hpolar
  have hp : ∀ᵐ ω ∂P, μ ω (annulus z (3 * r) (5 * r)) ≠ 0 ∧
      μ ω (annulus z (3 * r) (5 * r)) ≠ ∞ := by
    filter_upwards [hpositive, hfinite] with ω hp hf
    exact ⟨hp.ne', hf⟩
  exact exists_normalizedRestriction_version_of_ae_piSystem_ratios P
    (fieldSigmaAlgebraModConst 0 hC U) hm μ hμ _
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet hp S hcount hgen hpi hsets hversion

end HarmonicBalls.Section6
