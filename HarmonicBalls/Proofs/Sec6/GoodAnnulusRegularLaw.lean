import HarmonicBalls.Proofs.Sec6.GoodAnnulusNullMeasurable
import HarmonicBalls.Proofs.Sec6.GoodAnnulusAffineLaw

/-! # Good-annulus laws using regular representatives

Full support and nonatomicity provide the regularity needed to compare
probabilities through the measurable good-annulus representative.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology MarkovProcess ProbabilityTheory
open scoped ENNReal NNReal

universe u

/-- An LQG measure is almost surely nonatomic and has finite, positive mass
on any nonempty annulus. -/
theorem ae_lqg_goodAnnulus_regular
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) :
    ∀ᵐ ω ∂P, (∀ x : ℂ, μ ω {x} = 0) ∧
      μ ω (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
      0 < ENNReal.ofReal a * μ ω (annulus z (3 * r) (5 * r)) := by
  have hnonempty : (annulus z (3 * r) (5 * r)).Nonempty := by
    refine ⟨z + (((4 * r : ℝ) : ℂ)), ?_⟩
    have hd : dist (z + (((4 * r : ℝ) : ℂ))) z = 4 * r := by
      simp [dist_eq_norm, hr.le]
    change dist (z + (((4 * r : ℝ) : ℂ))) z < 5 * r ∧
      ¬ dist (z + (((4 * r : ℝ) : ℂ))) z ≤ 3 * r
    rw [hd]
    constructor <;> linarith
  filter_upwards [hatom h hγ hγ2 hα μ hμ,
    hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ, hμ] with ω hωatom hωfull hωloc
  let : IsLocallyFiniteMeasure (μ ω) := hωloc.isLocallyFiniteMeasure
  have hpos := hωfull _ (isOpen_ball.sdiff isClosed_closedBall) hnonempty
  have hfinite : μ ω (annulus z (3 * r) (5 * r)) ≠ ∞ :=
    ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset)
  exact ⟨hωatom, hfinite, ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' hpos.ne'⟩

/-- The bad good-annulus probability is independent of the centre and scale
under the affine laws and Brownian point avoidance. -/
theorem badGoodAnnulus_probability_eq_unit_of_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) {a : ℝ} (ha : 0 < a) (b : ℝ)
    (hatomAffine : LQGMeasureNonatomic P γ 0 (affinePairing hC hcirc (r : ℂ) z)
      (affineCircle hcirc (r : ℂ) z))
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} =
      P {ω | ¬ IsGoodAnnulus (μ ω) 1 0 a b} := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hs := hAff h (r : ℂ) hr0 z
  have hμs := isLQGMeasureOfField_affine hCC h hγ hγ2 hμ hr0 z
  have hd := identDistrib_affineMeasure h hμ hAff hCC hγ hγ2 hr0 z
  have hsmall := annulus_smallBallHitting_of_ae_point_avoidance 1 (by norm_num) 0 hpolar
  have heq := badGoodAnnulus_probability_eq_of_identDistrib_of_regular hd
    (r := 1) (by norm_num) 0 a b hsmall
    (ae_lqg_goodAnnulus_regular hfull hγ hγ2 hQ h hμ hatom (by norm_num) 0 ha)
    (ae_lqg_goodAnnulus_regular hfull hγ hγ2 hQ hs hμs hatomAffine (by norm_num) 0 ha)
  have hset : {ω | ¬ IsGoodAnnulus (affineMeasure γ hcirc μ (r : ℂ) z ω) 1 0 a b} =
      {ω | ¬ IsGoodAnnulus (μ ω) r z a b} := by
    ext ω
    exact not_congr (isGoodAnnulus_affineMeasure_unit γ hcirc μ hr z a b ω)
  rw [hset] at heq
  exact heq.symm

/-- One reference field supplies a threshold for every realization, centre,
and positive scale. Nonatomicity is assumed for each field to which the
staged affine coordinate-change theorem is applied. -/
theorem exists_universal_goodAnnulus_probability_of_ae_unit_of_point_avoidance
    (hfull : LQGMeasureFullSupportStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hatom : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ 0 hC hcirc)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    (b : ℝ)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) (4 * 1),
      ∀ x ∈ annulus 0 (3 * 1) (5 * 1), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hae : ∀ᵐ ω ∂P₀, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ₀ ω) 1 0 a b)
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ 0 hC hcirc →
      ∀ r : ℝ, 0 < r → ∀ z : ℂ,
        P {ω | ¬ IsGoodAnnulus (μ ω) r z a b} ≤ ENNReal.ofReal (1 - p) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨a, ha, hbound⟩ := exists_lqg_goodAnnulus_threshold_of_ae_point_avoidance
    hfull hγ hγ2 hQ h₀ hμ₀ (hatom Ω₀ P₀ hC₀ hcirc₀) (by norm_num) 0 b hpolar hae hp
  refine ⟨a, ha, ?_⟩
  intro Ω _ P hC hcirc μ h hμ hAff hCC r hr z
  rw [badGoodAnnulus_probability_eq_unit_of_point_avoidance hfull hγ hγ2 h hμ hAff hCC
    (hatom Ω P hC hcirc) hr z ha.1 b
    (hatom Ω P (affinePairing hC hcirc (r : ℂ) z) (affineCircle hcirc (r : ℂ) z)) hpolar]
  have hsmall := annulus_smallBallHitting_of_ae_point_avoidance 1 (by norm_num) 0 hpolar
  have hd := h₀.identDistrib_lqgMeasure_across_spaces h hμ₀ hμ
  have heq := badGoodAnnulus_probability_eq_of_identDistrib_of_regular hd
    (r := 1) (by norm_num) 0 a b hsmall
    (ae_lqg_goodAnnulus_regular hfull hγ hγ2 hQ h₀ hμ₀
      (hatom Ω₀ P₀ hC₀ hcirc₀) (by norm_num) 0 ha.1)
    (ae_lqg_goodAnnulus_regular hfull hγ hγ2 hQ h hμ
      (hatom Ω P hC hcirc) (by norm_num) 0 ha.1)
  rw [← heq]
  exact hbound

end HarmonicBalls.Section6
