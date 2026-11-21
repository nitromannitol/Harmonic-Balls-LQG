import HarmonicBalls.Proofs.Potential.LQGClockExitIncrementDecomposition
import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement

/-! # Uniform integrability of exit-time clocks from unit-horizon increments

Let the field have jointly measurable circle averages that are continuous in the point at every
dyadic scale. If the expected increments of the dyadic clock approximations stopped at the exit
time from a bounded open domain `D` and capped at time one are bounded, uniformly over starting
points in `D`, by a summable sequence, then for almost every field the exit-time clock
approximations from a fixed start are dominated by one integrable function, hence uniformly
integrable. Together with an LQG clock that is a time-change clock, this gives convergence of
the expected Green integrals of the approximating measures to the expected exit time of
Liouville Brownian motion.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem measurable_lqgClockApprox_exit {γ : ℝ} {hε : ℝ → ℂ → ℝ} {D : Set ℂ}
    (hD : IsOpen D) (k : ℕ) (hc : Continuous (hε (dyadicScale k))) :
    Measurable (fun b => lqgClockApprox γ hε (dyadicScale k) b
      (ContinuousPath.exitTime D b).toNNReal) := by
  let g : ℂ → ℝ := fun y => dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε (dyadicScale k) y)
  have hg : Continuous g := continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc))
  simpa only [lqgClockApprox, g, SubMarkovKernelSemigroup.feynmanKacAdditiveFunctional,
    Function.comp_def, id_eq] using
    (SubMarkovKernelSemigroup.stronglyMeasurable_feynmanKacAdditiveFunctional_joint
      hg.measurable).measurable.comp
      ((ContinuousPath.measurable_exitTime D hD).ennreal_toNNReal.prodMk measurable_id)

/-- Summable unit-horizon increment bounds, uniform over starting points in a bounded open
domain, make the exit-time clock approximations uniformly integrable for almost every field. -/
theorem ae_uniformIntegrable_exit_clockApprox_of_unit_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] {γ : ℝ}
    (hε : Ω → ℝ → ℂ → ℝ)
    (hεm : ∀ k : ℕ, Measurable (fun p : Ω × ℂ => hε p.1 (dyadicScale k) p.2))
    (hεc : ∀ (k : ℕ) (ω : Ω), Continuous (hε ω (dyadicScale k)))
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (x : ℂ)
    (c : ℕ → ℝ≥0∞) (hcs : (∑' k, c k) ≠ ⊤)
    (hc : ∀ (k : ℕ), ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal
      |lqgClockApprox γ (hε p.1) (dyadicScale (k+1)) p.2
          (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal -
        lqgClockApprox γ (hε p.1) (dyadicScale k) p.2
          (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal|
      ∂(P.prod (planarBrownianMotion y))) ≤ c k) :
    ∀ᵐ ω ∂P, UniformIntegrable (fun k : ℕ => fun b =>
      lqgClockApprox γ (hε ω) (dyadicScale k) b (ContinuousPath.exitTime D b).toNNReal) 1
      (planarBrownianMotion x) := by
  let μ := planarBrownianMotion x
  let τ : ContinuousPath ℂ → ℝ≥0∞ := ContinuousPath.exitTime D
  have hτm : Measurable τ := ContinuousPath.measurable_exitTime D hD
  have hEτ : (∫⁻ b, τ b ∂μ) ≠ ⊤ :=
    (GreenOccupation.lintegral_exitTime_planarBrownianMotion_lt_top hD hDb x).ne
  have hfin : ∀ᵐ b ∂μ, τ b ≠ ⊤ := (ae_lt_top hτm hEτ).mono fun _ h => h.ne
  let f : ℕ → Ω × ℂ → ℝ := fun k p =>
    dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε p.1 (dyadicScale k) p.2)
  have hfm (k : ℕ) : Measurable (f k) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul (hεm k)))
  have hfc (k : ℕ) (ω : Ω) : Continuous (fun z => f k (ω, z)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hεc k ω)))
  let d : ℕ → Ω × ℂ → ℝ := fun k p => f (k+1) p - f k p
  have hdm (k : ℕ) : Measurable (d k) := (hfm (k+1)).sub (hfm k)
  have hdc (k : ℕ) (ω : Ω) : Continuous (fun z => d k (ω, z)) := (hfc (k+1) ω).sub (hfc k ω)
  have happrox (k : ℕ) (ω : Ω) (b : ContinuousPath ℂ) (u : ℝ) (hu : 0 ≤ u) :
      lqgClockApprox γ (hε ω) (dyadicScale k) b u.toNNReal =
        ∫ s in (0 : ℝ)..u, f k (ω, b s.toNNReal) := by
    simp only [lqgClockApprox, Real.coe_toNNReal _ hu, f]
  have hdiff (k : ℕ) (ω : Ω) (b : ContinuousPath ℂ) (u : ℝ) (hu : 0 ≤ u) :
      lqgClockApprox γ (hε ω) (dyadicScale (k+1)) b u.toNNReal -
        lqgClockApprox γ (hε ω) (dyadicScale k) b u.toNNReal =
        ∫ s in (0 : ℝ)..u, d k (ω, b s.toNNReal) := by
    have hpath : Continuous (fun s : ℝ => b s.toNNReal) :=
      b.continuous.comp continuous_real_toNNReal
    have h1 : IntervalIntegrable (fun s : ℝ => f (k+1) (ω, b s.toNNReal)) volume 0 u :=
      ((hfc (k+1) ω).comp hpath).intervalIntegrable _ _
    have h2 : IntervalIntegrable (fun s : ℝ => f k (ω, b s.toNNReal)) volume 0 u :=
      ((hfc k ω).comp hpath).intervalIntegrable _ _
    rw [happrox (k+1) ω b u hu, happrox k ω b u hu, ← intervalIntegral.integral_sub h1 h2]
  have hexit (k : ℕ) : (∫⁻ p, ENNReal.ofReal |∫ s in (0 : ℝ)..(τ p.2).toReal,
      d k (p.1, p.2 s.toNNReal)| ∂(P.prod μ)) ≤ c k * ∫⁻ b, (τ b + 1) ∂μ := by
    apply lintegral_ofReal_abs_exit_integral_le_of_unit hD x (d k) (hdm k) (hdc k) (c k) _ hfin
    intro y hy
    refine le_trans (le_of_eq ?_) (hc k y hy)
    apply lintegral_congr
    intro p
    rw [hdiff k p.1 p.2 (min 1 (ContinuousPath.exitTime D p.2).toReal)
      (le_min zero_le_one ENNReal.toReal_nonneg)]
  let Δ : ℕ → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun k p =>
    ENNReal.ofReal |∫ s in (0 : ℝ)..(τ p.2).toReal, d k (p.1, p.2 s.toNNReal)|
  have hΔm (k : ℕ) : Measurable (Δ k) :=
    ((measurable_intervalIntegral_path (d k) (hdm k) (fun b => (τ b).toReal)
      hτm.ennreal_toReal (fun _ => ENNReal.toReal_nonneg)).abs).ennreal_ofReal
  have hτ1 : (∫⁻ b, (τ b + 1) ∂μ) ≠ ⊤ := by
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    exact ENNReal.add_ne_top.mpr ⟨hEτ, ENNReal.one_ne_top⟩
  have hsumΔ : (∫⁻ p, ∑' k, Δ k p ∂(P.prod μ)) ≠ ⊤ := by
    rw [lintegral_tsum (fun k => (hΔm k).aemeasurable)]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hexit)
    rw [ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hcs hτ1
  have hΔsm : Measurable (fun p => ∑' k, Δ k p) := Measurable.tsum hΔm
  have hquench : ∀ᵐ ω ∂P, (∫⁻ b, ∑' k, Δ k (ω, b) ∂μ) ≠ ⊤ := by
    have h := lintegral_prod _ hΔsm.aemeasurable (μ := P) (ν := μ)
    rw [h] at hsumΔ
    exact (ae_lt_top hΔsm.lintegral_prod_right' hsumΔ).mono fun _ h => h.ne
  filter_upwards [hquench] with ω hω
  let A : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    lqgClockApprox γ (hε ω) (dyadicScale k) b (τ b).toNNReal
  have hAm (k : ℕ) : Measurable (A k) := measurable_lqgClockApprox_exit hD k (hεc k ω)
  obtain ⟨M₁, hM₁⟩ := (hDb.isCompact_closure).exists_bound_of_continuousOn
    (hfc 0 ω).continuousOn
  set M : ℝ := max M₁ 0
  have hM : ∀ z ∈ closure D, ‖f 0 (ω, z)‖ ≤ M := fun z hz => (hM₁ z hz).trans (le_max_left _ _)
  have hM0 : 0 ≤ M := le_max_right _ _
  have hA0 (b : ContinuousPath ℂ) (hb : τ b ≠ ⊤) : ‖A 0 b‖ ≤ M * (τ b).toReal := by
    have hrepr : A 0 b = ∫ s in (0 : ℝ)..(τ b).toReal, f 0 (ω, b s.toNNReal) := by
      have hconv : ((τ b).toReal).toNNReal = (τ b).toNNReal := Real.toNNReal_coe
      have h := happrox 0 ω b _ (ENNReal.toReal_nonneg (a := τ b))
      rw [hconv] at h
      exact h
    rw [hrepr]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := 0) (b := (τ b).toReal) (C := M) (f := fun s => f 0 (ω, b s.toNNReal)) ?_
    · rwa [sub_zero, abs_of_nonneg ENNReal.toReal_nonneg] at h
    · filter_upwards [(volume : Measure ℝ).ae_ne (τ b).toReal] with s hs hsI
      rw [uIoc_of_le ENNReal.toReal_nonneg] at hsI
      have hlt : s < (τ b).toReal := lt_of_le_of_ne hsI.2 hs
      have hmem : b s.toNNReal ∈ D := by
        apply ContinuousPath.mem_of_lt_exitTime D b
        have h' : ENNReal.ofReal s < ENNReal.ofReal (τ b).toReal :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hsI.1.le).mpr hlt
        rw [ENNReal.ofReal_toReal hb] at h'
        exact h'
      exact hM _ (subset_closure hmem)
  let Y : ContinuousPath ℂ → ℝ≥0∞ := fun b => ENNReal.ofReal (M * (τ b).toReal) + ∑' k, Δ k (ω, b)
  have hS : Measurable (fun b => ∑' k, Δ k (ω, b)) :=
    Measurable.tsum fun k => (hΔm k).comp measurable_prodMk_left
  have hYm : Measurable Y :=
    (measurable_const.mul hτm.ennreal_toReal).ennreal_ofReal.add hS
  have hYi : (∫⁻ b, Y b ∂μ) ≠ ⊤ := by
    rw [lintegral_add_right' _ hS.aemeasurable]
    refine ENNReal.add_ne_top.mpr ⟨?_, hω⟩
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := M)) hEτ) ?_
    rw [← lintegral_const_mul _ hτm]
    apply lintegral_mono
    intro b
    simp only
    rw [ENNReal.ofReal_mul hM0]
    exact mul_le_mul_of_nonneg_left ENNReal.ofReal_toReal_le zero_le
  have hdom (k : ℕ) : ∀ᵐ b ∂μ, ENNReal.ofReal ‖A k b‖ ≤ Y b := by
    filter_upwards [hfin] with b hb
    have htel : A k b = A 0 b + ∑ j ∈ Finset.range k, (A (j+1) b - A j b) := by
      rw [Finset.sum_range_sub (fun j => A j b)]
      ring
    have hΔj (j : ℕ) : ENNReal.ofReal |A (j+1) b - A j b| = Δ j (ω, b) := by
      have hconv : ((τ b).toReal).toNNReal = (τ b).toNNReal := Real.toNNReal_coe
      have h := hdiff j ω b _ (ENNReal.toReal_nonneg (a := τ b))
      rw [hconv] at h
      simp only [A, Δ]
      rw [h]
    calc
      ENNReal.ofReal ‖A k b‖ ≤ ENNReal.ofReal (‖A 0 b‖ +
          ∑ j ∈ Finset.range k, |A (j+1) b - A j b|) := by
        apply ENNReal.ofReal_le_ofReal
        rw [htel, Real.norm_eq_abs, Real.norm_eq_abs]
        exact (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ = ENNReal.ofReal ‖A 0 b‖ + ∑ j ∈ Finset.range k, ENNReal.ofReal |A (j+1) b - A j b| := by
        rw [ENNReal.ofReal_add (norm_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _),
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      _ ≤ ENNReal.ofReal (M * (τ b).toReal) + ∑' j, Δ j (ω, b) := by
        apply add_le_add (ENNReal.ofReal_le_ofReal (hA0 b hb))
        simp only [hΔj]
        exact ENNReal.sum_le_tsum _
  let Yr : ContinuousPath ℂ → ℝ := fun b => (Y b).toReal
  have hYr : MemLp Yr 1 μ := by
    rw [memLp_one_iff_integrable]
    exact integrable_toReal_of_lintegral_ne_top hYm.aemeasurable hYi
  have hYfin : ∀ᵐ b ∂μ, Y b ≠ ⊤ := (ae_lt_top hYm hYi).mono fun _ h => h.ne
  have hdomr (k : ℕ) : ∀ᵐ b ∂μ, ‖A k b‖ ≤ ‖Yr b‖ := by
    filter_upwards [hdom k, hYfin] with b hb hbf
    rw [Real.norm_eq_abs (Yr b), abs_of_nonneg ENNReal.toReal_nonneg]
    have := ENNReal.toReal_mono hbf hb
    rwa [ENNReal.toReal_ofReal (norm_nonneg _)] at this
  refine ⟨?_, ?_⟩
  · refine (unifIntegrable_const le_rfl ENNReal.one_ne_top hYr (ι := ℕ)).ae_mono
      (fun k => (hAm k).aestronglyMeasurable) (fun k => ?_)
    filter_upwards [hdomr k] with b hb
    exact enorm_le_iff_norm_le.mpr hb
  · refine ⟨(eLpNorm Yr 1 μ).toNNReal, fun k => ?_⟩
    rw [ENNReal.coe_toNNReal hYr.eLpNorm_lt_top.ne]
    exact eLpNorm_mono_ae (hAm k).aestronglyMeasurable (hdomr k)


/-- Under summable unit-horizon increment bounds, uniform over starts in a smooth bounded
domain, for almost every field every LQG clock from a fixed start in the domain that is almost
surely a time-change clock has finite expected LBM exit time, and this expected exit time is the
limit of the expected Green integrals of the approximating measures. -/
theorem ae_tendsto_clockApprox_green_expectedLBMExitTime_of_unit_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P] {γ : ℝ}
    (hε : Ω → ℝ → ℂ → ℝ)
    (hεm : ∀ k : ℕ, Measurable (fun p : Ω × ℂ => hε p.1 (dyadicScale k) p.2))
    (hεc : ∀ (k : ℕ) (ω : Ω), Continuous (hε ω (dyadicScale k)))
    {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    (c : ℕ → ℝ≥0∞) (hcs : (∑' k, c k) ≠ ⊤)
    (hc : ∀ (k : ℕ), ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal
      |lqgClockApprox γ (hε p.1) (dyadicScale (k+1)) p.2
          (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal -
        lqgClockApprox γ (hε p.1) (dyadicScale k) p.2
          (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal|
      ∂(P.prod (planarBrownianMotion y))) ≤ c k)
    (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hclock : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (hε ω) x (F ω))
    (hF : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, expectedLBMExitTime (F ω) D x ≠ ⊤ ∧
      Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * hε ω (dyadicScale k) y)))
        atTop (𝓝 (expectedLBMExitTime (F ω) D x)) := by
  have hDo : IsOpen D := GreenGeneral.isOpen_of_isSmoothBoundedOpen hD
  filter_upwards [hclock, hF,
    ae_uniformIntegrable_exit_clockApprox_of_unit_increments hε hεm hεc hDo hD.1 x c hcs hc]
    with ω h1 h2 h3
  obtain ⟨-, -, hne, -, htend⟩ :=
    tendsto_clockApprox_green_expectedLBMExitTime_of_uniformIntegrable hD hx
      (fun k => hεc k ω) h1 h2 h3
  exact ⟨hne, htend⟩

/-- The expected exit-time identity for the inserted circle averages of the whole-plane
Gaussian free field: under summable unit-horizon increment bounds for the actual clocks,
uniform over starts in a smooth bounded domain, for almost every field every LQG clock from a
fixed start in the domain that is almost surely a time-change clock has finite expected LBM
exit time, equal to the limit of the expected Green integrals of the approximating measures. -/
theorem ae_tendsto_clockApprox_green_expectedLBMExitTime_fieldCircleAverage_of_unit_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    {D : Set ℂ} (hD : IsSmoothBoundedOpen D) {x : ℂ} (hx : x ∈ D)
    (c : ℕ → ℝ≥0∞) (hcs : (∑' k, c k) ≠ ⊤)
    (hc : ∀ (k : ℕ), ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal
      |lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1)) (dyadicScale (k+1))
          p.2 (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal -
        lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1)) (dyadicScale k)
          p.2 (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal|
      ∂(P.prod (planarBrownianMotion y))) ≤ c k)
    (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hclock : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) x (F ω))
    (hF : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), IsTimeChangeClock (F ω b)) :
    ∀ᵐ ω ∂P, expectedLBMExitTime (F ω) D x ≠ ⊤ ∧
      Tendsto (fun k : ℕ => ∫⁻ y, ENNReal.ofReal (2 * greenFunction D x y) *
        ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) y)))
        atTop (𝓝 (expectedLBMExitTime (F ω) D x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let H' : Ω → ℝ → ℂ → ℝ := fun ω r z => H ω r z - H ω 1 0 - α * Real.log (max r ‖z‖)
  have hH'm (k : ℕ) : Measurable (fun p : Ω × ℂ => H' p.1 (dyadicScale k) p.2) := by
    have h1 : Measurable (fun p : Ω × ℂ => H p.1 (dyadicScale k) p.2) :=
      (hHm _ (dyadicScale_pos k)).comp measurable_swap
    have h2 : Measurable (fun p : Ω × ℂ => H p.1 1 0) :=
      (hHm 1 one_pos).comp ((measurable_const : Measurable fun _ : Ω × ℂ => (0 : ℂ)).prodMk
        measurable_fst)
    have h3 : Measurable (fun p : Ω × ℂ => α * Real.log (max (dyadicScale k) ‖p.2‖)) :=
      measurable_const.mul (Real.measurable_log.comp
        (measurable_const.max (measurable_norm.comp measurable_snd)))
    exact (h1.sub h2).sub h3
  have hH'c (k : ℕ) (ω : Ω) : Continuous (H' ω (dyadicScale k)) :=
    ((hHc ω _ (dyadicScale_pos k)).sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne')))
  have hae : ∀ᵐ ω ∂P, ∀ k : ℕ, H' ω (dyadicScale k) =
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hr k
    funext z
    simp only [H', hω]
    exact hr _ z (dyadicScale_pos k)
  have happ : ∀ᵐ ω ∂P, ∀ k : ℕ, lqgClockApprox γ (H' ω) (dyadicScale k) =
      lqgClockApprox γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) (dyadicScale k) := by
    filter_upwards [hae] with ω hω k
    funext b t
    simp only [lqgClockApprox, hω k]
  have hc' : ∀ (k : ℕ), ∀ y ∈ D, (∫⁻ p, ENNReal.ofReal
      |lqgClockApprox γ (H' p.1) (dyadicScale (k+1)) p.2
          (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal -
        lqgClockApprox γ (H' p.1) (dyadicScale k) p.2
          (min 1 (ContinuousPath.exitTime D p.2).toReal).toNNReal|
      ∂(P.prod (planarBrownianMotion y))) ≤ c k := by
    intro k y hy
    refine le_trans (le_of_eq ?_) (hc k y hy)
    apply lintegral_congr_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion y)).ae happ] with p hp
    rw [hp (k+1), hp k]
  have hclock' : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ (H' ω) x (F ω) := by
    filter_upwards [hclock, happ] with ω h hω
    intro T η hη
    simpa only [hω] using h T η hη
  filter_upwards [ae_tendsto_clockApprox_green_expectedLBMExitTime_of_unit_increments H' hH'm
    hH'c hD hx c hcs hc' F hclock' hF, hae] with ω h hω
  simpa only [hω] using h
end HarmonicBalls
