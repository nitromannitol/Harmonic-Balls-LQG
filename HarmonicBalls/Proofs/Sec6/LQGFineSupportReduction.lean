import HarmonicBalls.Proofs.Sec6.FineSupportCompactReduction
import HarmonicBalls.Proofs.Sec6.GoodAnnulusMeanValue

/-! # LQG fine-support reduction

The recurrence of Green-potential ratios combines with the compact hitting
reduction. The pre-exit hitting estimate and the Brownian zero-one property
remain explicit hypotheses.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal Topology

/-- The geometric scales used for fine-support annuli tend to zero. -/
theorem tendsto_fineSupportScale_zero : Tendsto fineSupportScale atTop (𝓝 0) := by
  unfold fineSupportScale
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The geometric scales used for fine-support annuli decrease. -/
theorem antitone_fineSupportScale : Antitone fineSupportScale := by
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn

universe u

/-- Fine support at almost every centre follows from the potential hitting
bound and the zero-one property, together with the staged LQG inputs. -/
theorem ae_ae_lqg_fine_support_of_hitting_bounds
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hbound : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      (μ ω) (ball x ε \ ⋃ n, K n) = 0 →
      ∀ᶠ n in atTop,
        ENNReal.ofReal (greenPotentialExtremaRatio (fineSupportAnnulus x (fineSupportScale n))
          (sphere x (fineSupportScale n / 4)) (μ ω)) ≤ planarBrownianMotion x
        {ω' | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω' ≤
          ContinuousPath.exitTime (ball x (fineSupportScale n)) ω'})
    (hzeroOne : ∀ x : ℂ, ∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Monotone K →
      0 < planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0} →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ ω) (ball x ε \ E) = 0 →
      ∀ᵐ ω' ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω' = 0 := by
  have hrec := ae_ae_fineSupport_ratio_recurs_of_gff_joint
    hholder hfull hgrowth hγ hγ2 h hμ hnonatom hAff hCC
  filter_upwards [hrec, hbound, hμ] with ω hrecω hboundω hμω
  let : IsLocallyFiniteMeasure (μ ω) := hμω.isLocallyFiniteMeasure
  filter_upwards [hrecω, hboundω] with x hrecx hboundx
  intro ε hε E hE hmass
  exact ae_instant_hit_of_recurrent_lower_bounds
    (measure_ball_ne_top (μ := μ ω) (x := x) (r := ε))
    tendsto_fineSupportScale_zero antitone_fineSupportScale hrecx
    (hboundx ε hε) (hzeroOne x) hE hmass

/-- Local fine support implies instant hitting of every Borel set of full mass
in an open domain, from almost every point of a measurable subset. -/
theorem ae_instant_hit_of_ae_local_fine_support
    (μ : Measure ℂ) {A S : Set ℂ} (hA : IsOpen A) (hS : MeasurableSet S) (hSA : S ⊆ A)
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {E : Set ℂ} (hE : MeasurableSet E) (hfull : μ (A \ E) = 0) :
    ∀ᵐ x ∂(volume.restrict S), ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime Eᶜ ω = 0 := by
  filter_upwards [ae_restrict_of_ae hloc, ae_restrict_mem hS] with x hx hxS
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hA x (hSA hxS)
  apply hx ε hε E hE
  apply measure_mono_null _ hfull
  intro y hy
  exact ⟨hball hy.1, hy.2⟩

/-- Local fine support and a ball submean estimate give a positive
mass threshold for a good annulus. -/
theorem exists_goodAnnulus_threshold_of_ae_local_fine_support
    (μ : Measure ℂ) {z : ℂ} {r b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hloc : ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → μ (ball x ε \ E) = 0 →
      ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere z (4 * r),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (r / 4), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume) :
    ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus μ r z a b := by
  apply exists_goodAnnulus_threshold_of_ball_submean μ hr hb hfinite ?_ hC0 hCtop hsubmean
  intro E hE hmass
  exact ae_instant_hit_of_ae_local_fine_support μ (isOpen_ball.sdiff isClosed_closedBall)
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    (innerAnnulus_subset_goodAnnulus z hr) hloc hE hmass

/-- Almost-sure local fine support gives almost-sure positive good-annulus
thresholds under the ball submean estimate. -/
theorem ae_exists_goodAnnulus_threshold_of_ae_local_fine_support
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (μ : Ω → Measure ℂ)
    {z : ℂ} {r b : ℝ} (hr : 0 < r) (hb : 0 < b)
    (hfinite : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hloc : ∀ᵐ ω ∂P, ∀ᵐ x ∂(volume : Measure ℂ), ∀ ε : ℝ, 0 < ε →
      ∀ E : Set ℂ, MeasurableSet E → (μ ω) (ball x ε \ E) = 0 →
      ∀ᵐ ω' ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω' = 0)
    {C : ℝ≥0∞} (hC0 : C ≠ 0) (hCtop : C ≠ ∞)
    (hsubmean : ∀ K : Set ℂ, IsCompact K → ∀ u ∈ sphere z (4 * r),
      planarBrownianMotion u
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ≤
      C * ∫⁻ x in ball u (r / 4), planarBrownianMotion x
        {ω | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) ω ≤
          ContinuousPath.exitTime Kᶜ ω} ∂volume) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ IsGoodAnnulus (μ ω) r z a b := by
  filter_upwards [hfinite, hloc] with ω hfiniteω hlocω
  let : IsLocallyFiniteMeasure (μ ω) := hfiniteω
  apply exists_goodAnnulus_threshold_of_ae_local_fine_support (μ ω) hr hb ?_ hlocω
    hC0 hCtop hsubmean
  exact ne_top_of_le_ne_top (measure_ball_ne_top (μ := μ ω)) (measure_mono sdiff_subset)

end HarmonicBalls.Section6
