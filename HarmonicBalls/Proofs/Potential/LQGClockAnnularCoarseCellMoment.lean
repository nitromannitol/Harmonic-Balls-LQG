import HarmonicBalls.Proofs.Potential.LQGClockAnnularCellSecondMoment

/-! # Coarse-scale annular cell moments

Gaussian moment bounds at smoothing scales bounded away from zero control
annular clock cells uniformly in their position and Brownian starting point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A circle average on a bounded disc has a uniform exponential moment when
its radius stays in a compact interval away from zero. -/
theorem integral_exp_circle_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε : ε ≤ 1)
    (γ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    (∫ ω, Real.exp (γ * hcirc ω ε z) ∂P) ≤
      Real.exp ((γ ^ 2 / 2) * (-Real.log η + 2 * Real.log 3)) := by
  have he : 0 < ε := hη.trans_le hηε
  have h := hh.integral_exp_sum_circle he (fun _ : Fin 1 => z) (fun _ => γ)
  simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] at h
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hv := hh.variance_circle_le he hε hz
  have hlog : Real.log η ≤ Real.log ε := Real.log_le_log hη hηε
  have hc : cov[fun ω => hcirc ω ε z, fun ω => hcirc ω ε z; P] =
      Var[fun ω => hcirc ω ε z; P] := covariance_self (hh.hasGaussianLaw_circle he z).aemeasurable
  rw [h, hc]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hv (sq_nonneg γ),
    mul_le_mul_of_nonneg_left (show -Real.log ε + 2 * Real.log 3 ≤
      -Real.log η + 2 * Real.log 3 by linarith) (sq_nonneg γ)]

/-- The inserted density has a uniform second moment on a bounded disc when
its smoothing scale is bounded away from zero. -/
theorem integral_inserted_clock_density_sq_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε : ε ≤ 1)
    (γ α : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    (∫ ω, (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) ^ 2 ∂P) ≤
      Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3)) := by
  have he : 0 < ε := hη.trans_le hηε
  have ht0 : 0 < max ε ‖z‖ := he.trans_le (le_max_left _ _)
  have ht1 : max ε ‖z‖ ≤ 1 := max_le hε (by linarith)
  have hlog : Real.log η ≤ Real.log (max ε ‖z‖) :=
    Real.log_le_log hη (hηε.trans (le_max_left _ _))
  have htlog : Real.log (max ε ‖z‖) ≤ 0 := Real.log_nonpos ht0.le ht1
  have hηlog : Real.log η ≤ 0 := hlog.trans htlog
  have hweight : Real.exp (-(γ * α) * Real.log (max ε ‖z‖)) ≤
      Real.exp (|γ * α| * |Real.log η|) := by
    apply Real.exp_le_exp.mpr
    calc
      -(γ * α) * Real.log (max ε ‖z‖) ≤
          |-(γ * α) * Real.log (max ε ‖z‖)| := le_abs_self _
      _ = |γ * α| * |Real.log (max ε ‖z‖)| := by rw [abs_mul, abs_neg]
      _ ≤ |γ * α| * |Real.log η| := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        rw [abs_of_nonpos htlog, abs_of_nonpos hηlog]
        linarith
  have hnorm : ε ^ (γ ^ 2 / 2) ≤ 1 := Real.rpow_le_one he.le hε (by positivity)
  have hexp : Integrable (fun ω => Real.exp ((2 * γ) * hcirc ω ε z)) P := by
    have h := hh.integrable_exp_sum_circle he (fun _ : Fin 1 => z) (fun _ => 2 * γ)
    simpa only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton] using h
  have hint : Integrable (fun ω => (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) ^ 2) P := by
    simpa only [pow_two] using integrable_inserted_clock_density_mul hh he γ α z z
  have hpoint : ∀ᵐ ω ∂P, (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) ^ 2 ≤
      Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp ((2 * γ) * hcirc ω ε z) := by
    filter_upwards [ae_recentered_inserted_circle_average hh α,
      hh.ae_circleAverage_one_zero] with ω hω hzero
    rw [← hω ε z he, hzero]
    simp only [sub_zero]
    have heq : γ * (hcirc ω ε z - α * Real.log (max ε ‖z‖)) =
        γ * hcirc ω ε z + (-(γ * α) * Real.log (max ε ‖z‖)) := by ring
    rw [heq, Real.exp_add]
    have hbase : ε ^ (γ ^ 2 / 2) * (Real.exp (γ * hcirc ω ε z) *
        Real.exp (-(γ * α) * Real.log (max ε ‖z‖))) ≤
        Real.exp (|γ * α| * |Real.log η|) * Real.exp (γ * hcirc ω ε z) := by
      calc
        _ ≤ 1 * (Real.exp (γ * hcirc ω ε z) *
            Real.exp (-(γ * α) * Real.log (max ε ‖z‖))) :=
              mul_le_mul_of_nonneg_right hnorm (by positivity)
        _ ≤ Real.exp (γ * hcirc ω ε z) *
            Real.exp (|γ * α| * |Real.log η|) := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_left hweight
                (Real.exp_pos (γ * hcirc ω ε z)).le
        _ = _ := mul_comm _ _
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ε ^ (γ ^ 2 / 2) *
      (Real.exp (γ * hcirc ω ε z) * Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) hbase 2
    have hexpeq : Real.exp ((2 * γ) * hcirc ω ε z) =
        Real.exp (γ * hcirc ω ε z) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    rw [hexpeq, mul_pow]
    simpa only [mul_pow] using hs
  calc
    _ ≤ ∫ ω, Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp ((2 * γ) * hcirc ω ε z) ∂P :=
          integral_mono_ae hint (hexp.const_mul _) hpoint
    _ = Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        (∫ ω, Real.exp ((2 * γ) * hcirc ω ε z) ∂P) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_exp_circle_le_of_scale_lower_bound hh hη hηε hε (2 * γ) (by linarith))
      (sq_nonneg _)

/-- Two inserted densities at bounded centers have a uniform product moment
when the smoothing scale is bounded away from zero. -/
theorem lintegral_inserted_clock_density_mul_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε : ε ≤ 1)
    (γ α : ℝ) {z w : ℂ} (hz : ‖z‖ ≤ 1 / 2) (hw : ‖w‖ ≤ 1 / 2) :
    (∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) *
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) ∂P) ≤
      ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3)))) := by
  have he : 0 < ε := hη.trans_le hηε
  let f : ℂ → Ω → ℝ := fun v ω => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε v)
  let K : ℝ := Real.exp (|γ * α| * |Real.log η|) ^ 2 *
    Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3))
  have hf (v : ℂ) (ω : Ω) : 0 ≤ f v ω := by dsimp [f]; positivity
  have hint (v u : ℂ) : Integrable (fun ω => f v ω * f u ω) P :=
    integrable_inserted_clock_density_mul hh he γ α v u
  have hsq (v : ℂ) : Integrable (fun ω => (f v ω) ^ 2) P := by
    simpa only [pow_two] using hint v v
  have hbound (v : ℂ) (hv : ‖v‖ ≤ 1 / 2) : (∫ ω, (f v ω) ^ 2 ∂P) ≤ K :=
    integral_inserted_clock_density_sq_le_of_scale_lower_bound hh hη hηε hε γ α hv
  have hprod : (∫ ω, f z ω * f w ω ∂P) ≤ 2 * K := by
    calc
      _ ≤ ∫ ω, ((f z ω) ^ 2 + (f w ω) ^ 2) ∂P := by
        apply integral_mono (hint z w) ((hsq z).add (hsq w))
        intro ω
        change f z ω * f w ω ≤ (f z ω) ^ 2 + (f w ω) ^ 2
        nlinarith [sq_nonneg (f z ω - f w ω), hf z ω, hf w ω]
      _ = (∫ ω, (f z ω) ^ 2 ∂P) + ∫ ω, (f w ω) ^ 2 ∂P :=
        integral_add (hsq z) (hsq w)
      _ ≤ 2 * K := by linarith [hbound z hz, hbound w hw]
  have heq : (∫⁻ ω, ENNReal.ofReal (f z ω) * ENNReal.ofReal (f w ω) ∂P) =
      ENNReal.ofReal (∫ ω, f z ω * f w ω ∂P) := by
    simp_rw [← ENNReal.ofReal_mul (hf z _)]
    exact (ofReal_integral_eq_lintegral_ofReal (hint z w)
      (Filter.Eventually.of_forall fun ω => mul_nonneg (hf z ω) (hf w ω))).symm
  change (∫⁻ ω, ENNReal.ofReal (f z ω) * ENNReal.ofReal (f w ω) ∂P) ≤ _
  rw [heq]
  exact ENNReal.ofReal_le_ofReal hprod

/-- The annular density product is uniformly bounded in expectation at coarse
smoothing scales, including coincident spatial points. -/
theorem lintegral_annular_inserted_clock_density_mul_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε : ε ≤ 1)
    (γ α δ : ℝ) (z w : ℂ) :
    (∫⁻ ω, ENNReal.ofReal
        ({u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) *
      ENNReal.ofReal
        ({u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) w) ∂P) ≤
      ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3)))) := by
  by_cases hz : δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2
  · by_cases hw : δ ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hz, ite_eq_left hw]
      exact lintegral_inserted_clock_density_mul_le_of_scale_lower_bound hh hη hηε hε γ α hz.2 hw.2
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hw,
        ENNReal.ofReal_zero, mul_zero, lintegral_zero]
      exact zero_le
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hz,
      ENNReal.ofReal_zero, zero_mul, lintegral_zero]
    exact zero_le

/-- The second moment of annular mass against an s-finite measure is bounded
by a constant times the square of its total mass at coarse scales. -/
theorem lintegral_annular_inserted_mass_sq_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure ℂ) [SFinite ν] {η ε : ℝ} (hη : 0 < η)
    (hηε : η ≤ ε) (hε : ε ≤ 1) (γ α δ : ℝ) :
    (∫⁻ ω, (∫⁻ z, ENNReal.ofReal
        ({u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) ∂ν) ^ 2 ∂P) ≤
      ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3)))) * (ν Set.univ) ^ 2 := by
  have hεpos : 0 < ε := hη.trans_le hηε
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}
  let f : ℂ → Ω → ℝ≥0∞ := fun z ω =>
    ENNReal.ofReal (A.indicator (fun u =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω ε u - H ω 1 0 -
        α * Real.log (max ε ‖u‖)))) z)
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hf : Measurable (Function.uncurry f) := by
    apply ENNReal.measurable_ofReal.comp
    have he : Measurable (fun p : ℂ × Ω => H p.2 ε p.1) := hHm ε hεpos
    have h1 : Measurable (fun p : ℂ × Ω => H p.2 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_snd)
    have hm : Measurable (fun p : ℂ × Ω =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.2 ε p.1 - H p.2 1 0 -
          α * Real.log (max ε ‖p.1‖)))) :=
      measurable_const.mul (measurable_const.mul ((he.sub h1).sub
        (measurable_const.mul ((measurable_const.max measurable_fst.norm).log)))).exp
    convert hm.indicator (measurable_fst hA) using 1
    ext p
    rfl
  have hae : ∀ᵐ ω ∂P, ∀ z, f z ω = ENNReal.ofReal (A.indicator (fun u =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    intro z
    dsimp [f]
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε z hεpos]
    · rfl
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
    Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3))))
  have hK (z w : ℂ) : (∫⁻ ω, f z ω * f w ω ∂P) ≤ C := by
    have heq : (∫⁻ ω, f z ω * f w ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal (A.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) *
          ENNReal.ofReal (A.indicator (fun u =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) w) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω z, hω w]
    rw [heq]
    exact lintegral_annular_inserted_clock_density_mul_le_of_scale_lower_bound
      hh hη hηε hε γ α δ z w
  have hmain := lintegral_sq_lintegral_le_pair (P := P) (ν := ν) hf (fun _ _ => C) hK
  have heq : (∫⁻ ω, (∫⁻ z, f z ω ∂ν) ^ 2 ∂P) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (A.indicator (fun u =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) ∂ν) ^ 2 ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hae] with ω hω
    congr 1
    exact lintegral_congr fun z => hω z
  rw [heq] at hmain
  dsimp only [A, C] at hmain
  simpa only [lintegral_const, pow_two, mul_assoc] using hmain

/-- A Brownian annular time cell has a uniform second-moment bound at coarse
scales, with the square of its length. -/
theorem lintegral_prod_brownian_annular_cell_sq_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε : ε ≤ 1)
    (γ α δ u h : ℝ) :
    (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc u (u + h), ENNReal.ofReal
      ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))) ^ 2
          ∂(P.prod (planarBrownianMotion x))) ≤
      ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3)))) *
          (ENNReal.ofReal h) ^ 2 := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have he : 0 < ε := hη.trans_le hηε
  let A : Set ℂ := {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
    Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3))))
  let F : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun p =>
    ∫⁻ s in Ioc u (u + h), ENNReal.ofReal
      (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))
  have hF : AEMeasurable (fun p => (F p) ^ 2) (P.prod (planarBrownianMotion x)) :=
    (aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x) he γ α δ u (u+h)).pow_const 2
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hmeas : ∀ᵐ ω ∂P, Measurable (fun z => ENNReal.ofReal
      (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    have hm : Measurable (fun z : ℂ => ENNReal.ofReal
        (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          (H ω ε w - H ω 1 0 - α * Real.log (max ε ‖w‖)))) z)) := by
      apply ENNReal.measurable_ofReal.comp
      exact (measurable_const.mul (measurable_const.mul
        ((((hHm ε he).comp (measurable_id.prodMk measurable_const)).sub measurable_const).sub
          (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp).indicator hA
    convert hm using 1
    ext z
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε z he]
    · rfl
  have hbound (b : ContinuousPath ℂ) : (∫⁻ ω, (F (ω,b)) ^ 2 ∂P) ≤
      C * (ENNReal.ofReal h) ^ 2 := by
    let g : ℝ → ℂ := fun s => b s.toNNReal
    have hg : Measurable g := b.continuous.measurable.comp continuous_real_toNNReal.measurable
    let ν : Measure ℂ := Measure.map g (volume.restrict (Ioc u (u+h)))
    have hν : ν Set.univ = ENNReal.ofReal h := by
      rw [show ν = Measure.map g (volume.restrict (Ioc u (u+h))) from rfl,
        Measure.map_apply hg MeasurableSet.univ]
      simp only [preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioc]
      congr 1
      ring
    have heq : (∫⁻ ω, (F (ω,b)) ^ 2 ∂P) =
        ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (A.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z) ∂ν) ^ 2 ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hmeas] with ω hω
      dsimp [F, ν]
      rw [lintegral_map hω hg]
    rw [heq, ← hν]
    exact lintegral_annular_inserted_mass_sq_le_of_scale_lower_bound hh ν hη hηε hε γ α δ
  change (∫⁻ p, (F p) ^ 2 ∂(P.prod (planarBrownianMotion x))) ≤ _
  rw [lintegral_prod_symm _ hF]
  calc
    _ ≤ ∫⁻ _ : ContinuousPath ℂ, C * (ENNReal.ofReal h) ^ 2 ∂(planarBrownianMotion x) :=
      lintegral_mono hbound
    _ = _ := by
      simp only [lintegral_const, measure_univ, mul_one]
      rfl

/-- A finite family of dyadic scales has a uniform annular mesh-cell second
moment with the subcritical exponent, for every Brownian starting point. -/
theorem exists_lintegral_prod_annular_coarse_dyadic_mesh_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ2 : γ ^ 2 < 2) (α δ : ℝ) (N : ℕ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ 0 < (1 - γ ^ 2 / 2) / 2 ∧
      ∀ (k : ℕ), k ≤ N → ∀ (x : ℂ) (m : ℕ), 0 < m → ∀ j : Fin m,
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z))
              (p.2 s.toNNReal))) ^ (2 : ℝ) ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
  let η := dyadicScale N
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
    Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3))))
  refine ⟨C, ENNReal.ofReal_lt_top, by linarith, ?_⟩
  intro k hk x m hm j
  have hη : 0 < η := dyadicScale_pos N
  have hηk : η ≤ dyadicScale k := by
    dsimp only [η, dyadicScale]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
  have hk1 : dyadicScale k ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hend : ((j : ℝ) / m) + 1 / (m : ℝ) = ((j : ℝ) + 1) / m := by ring
  have hhalf : ENNReal.ofReal (1 / (m : ℝ)) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ((div_le_one₀ hm0).2 hm1)
  have hp : (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 : ℝ) ≤
      (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 - γ ^ 2 / 2) :=
    ENNReal.rpow_le_rpow_of_exponent_ge hhalf (by nlinarith [sq_nonneg γ])
  have hrpow : (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 - γ ^ 2 / 2) =
      (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hm0, ENNReal.ofReal_natCast,
      ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    congr 1
    ring
  have hmain := lintegral_prod_brownian_annular_cell_sq_le_of_scale_lower_bound
    hh x hη hηk hk1 γ α δ ((j : ℝ) / m) (1 / (m : ℝ))
  rw [hend] at hmain
  calc
    _ ≤ C * (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 : ℝ) := by
      simpa only [ENNReal.rpow_ofNat] using hmain
    _ ≤ C * (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
      rw [← hrpow]
      exact mul_le_mul' le_rfl hp

/-- The finitely many dyadic scales above the small-scale cutoff satisfy the
same subcritical annular mesh-cell moment bound, uniformly in the start. -/
theorem exists_lintegral_prod_annular_excluded_dyadic_mesh_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ2 : γ ^ 2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ 0 < (1 - γ ^ 2 / 2) / 2 ∧
      ∀ (k : ℕ), min (1 / 2) δ < dyadicScale k →
      ∀ (x : ℂ) (m : ℕ), 0 < m → ∀ j : Fin m,
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z))
              (p.2 s.toNNReal))) ^ (2 : ℝ) ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
  have hlim : Tendsto dyadicScale atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually
    (Iio_mem_nhds (lt_min (by norm_num : (0 : ℝ) < 1 / 2) hδ)))
  obtain ⟨C, hC, hβ, hbound⟩ :=
    exists_lintegral_prod_annular_coarse_dyadic_mesh_cell_sq_le hh hγ2 α δ N
  refine ⟨C, hC, hβ, ?_⟩
  intro k hk x m hm j
  have hkN : k ≤ N := by
    by_contra hn
    have hkn : N ≤ k := by omega
    exact (not_lt_of_ge (hN k hkn).le) hk
  exact hbound k hkN x m hm j

end HarmonicBalls
