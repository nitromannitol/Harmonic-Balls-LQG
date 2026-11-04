import HarmonicBalls.Proofs.Sec6.ArbitraryRadiusGoodAnnulus
import HarmonicBalls.Proofs.Sec6.SimultaneousSingularMeasure
import HarmonicBalls.Proofs.Sec6.VolumeGrowthNonatomic

/-! # Simultaneous positive good-annulus thresholds

The fine-support assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The LQG existence hypothesis is a staged input pending operator source review.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal

universe u

/-- A locally finite measure with almost-everywhere local fine support has a
positive good-annulus threshold simultaneously for every centre and radius. -/
theorem goodAnnulus_thresholds_of_ae_local_fine_support
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0) :
    ∀ (z : ℂ) (r b : ℝ), 0 < r → 0 < b →
      ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus μ r z a b := by
  intro z r b hr hb
  obtain ⟨C, hC0, hCt, hsub⟩ := goodAnnulus_avoidance_ball_submean (z := z) hr
  apply exists_goodAnnulus_threshold_of_ae_local_fine_support μ hr hb ?_ hloc hC0 hCt hsub
  exact ne_top_of_le_ne_top (measure_ball_ne_top (μ := μ)) (measure_mono sdiff_subset)

/-- For a whole-plane measure, positive thresholds exist on one full-measure
event for every choice of centre, radius and Brownian threshold. -/
theorem ae_all_goodAnnulus_thresholds_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (r b : ℝ), 0 < r → 0 < b →
      ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) r z a b := by
  let := h.isProbabilityMeasure
  have hloc := ae_ae_lqg_fine_support_of_disc_dyadic hgrowth hγ hγ2 h hμ
    (wholePlaneGFFAffineInvariance_proved P hC hcirc)
  filter_upwards [hμ, hloc] with ω hμω hlocω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  exact goodAnnulus_thresholds_of_ae_local_fine_support (μ ω) hlocω

/-- If the zero-strength measure exists, then on one full-measure event every
existing singular LQG limit has almost-everywhere local fine support. The
singularity strength need not be subcritical. -/
theorem ae_all_singular_fine_support_of_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
        ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
        ∀ᵐ ω' ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω' = 0 := by
  let := hG.isProbabilityMeasure
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨μ₀, hμ₀⟩ := hE0 hG hγ hγ2 hQ
  have hloc := ae_ae_lqg_fine_support_of_disc_dyadic hgrowth hγ hγ2 hG hμ₀
    (wholePlaneGFFAffineInvariance_proved P hC hcirc)
  have hnonatom := lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 hC hcirc
    hG hγ hγ2 hQ μ₀ hμ₀
  have hc0 : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos k))
  filter_upwards [hμ₀, hloc, hnonatom, hc0] with ω hbase hbaseLoc hno hc α μ hμ
  have hW : ∀ f : ℂ → ℝ, Continuous f →
      IsLQGLimit γ (addCircleAverage (fieldCircleAverage 0 (hcirc ω)) f)
        ((μ₀ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * f x))) :=
    fun f hf => isLQGLimit_addCircleAverage hbase hc f hf
  have hweight := restrict_compl_zero_eq_withDensity hμ hW
  let ν := (μ₀ ω).withDensity (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α))))
  have hνzero : ν {0} = 0 := (withDensity_absolutelyContinuous (μ₀ ω) _) (hno 0)
  have hνae : ∀ᵐ z ∂ν, z ∈ ({0} : Set ℂ)ᶜ := by simpa [ae_iff] using hνzero
  have hνrest : ν.restrict ({0} : Set ℂ)ᶜ = ν := Measure.restrict_eq_self_of_ae_mem hνae
  have hAC : μ₀ ω ≪ ν := absolutelyContinuous_singularWeight (hno 0) _
  have hbaseAC : μ₀ ω ≪ μ := by
    intro A hA
    apply hAC
    rw [← hνrest, ← hweight]
    exact le_zero_iff.mp ((Measure.restrict_le_self A).trans_eq hA)
  filter_upwards [hbaseLoc] with x hx ε hε E hE hmass
  exact hx ε hε E hE (hbaseAC hmass)

/-- The same full-measure event yields positive thresholds for all existing
singular LQG limits and every centre, radius and Brownian threshold. -/
theorem ae_all_singular_goodAnnulus_thresholds_of_zero_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hG : IsWholePlaneGFF P hC hcirc)
    (hE0 : LQGMeasureExistence P γ 0 hC hcirc) :
    ∀ᵐ ω ∂P, ∀ α : ℝ, ∀ μ : Measure ℂ,
      IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) μ →
      ∀ (z : ℂ) (r b : ℝ), 0 < r → 0 < b →
        ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus μ r z a b := by
  filter_upwards [ae_all_singular_fine_support_of_zero_existence
    hgrowth P γ hγ hγ2 hC hcirc hG hE0] with ω hloc α μ hμ
  let : IsLocallyFiniteMeasure μ := hμ.isLocallyFiniteMeasure
  exact goodAnnulus_thresholds_of_ae_local_fine_support μ (hloc α μ hμ)

end HarmonicBalls.Section6
