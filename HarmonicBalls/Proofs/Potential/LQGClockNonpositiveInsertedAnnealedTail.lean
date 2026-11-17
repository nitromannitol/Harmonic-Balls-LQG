import HarmonicBalls.Proofs.Potential.LQGClockNegativeInsertionWeightedIncrement

/-! # Nonpositive inserted inner clock increments

The smoothing-dependent correction admits a jointly measurable time integral.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The smoothing-dependent correction to a nonpositive inserted clock. -/
noncomputable def nonpositiveInsertionCorrection {Ω : Type*}
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ : ℝ) (n : ℕ)
    (q : ContinuousPath ℂ × Ω) : ℝ :=
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
    ((max ε ‖z‖) ^ (-γ*α) - (max (ε/2) ‖z‖) ^ (-γ*α)) *
      (ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) ε z))) (q.1 s.toNNReal)

/-- The actual correction time integrals have jointly measurable versions,
valid for every path and every dyadic scale on one full-field event. -/
theorem exists_measurable_nonpositive_insertion_corrections
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ)
    (δ : ℕ → ℝ) :
    ∃ F : ℕ → ContinuousPath ℂ × Ω → ℝ, (∀ n, Measurable (F n)) ∧
      ∀ᵐ ω ∂P, ∀ b n, F n (b, ω) =
        nonpositiveInsertionCorrection hcirc γ α (δ n) n (b, ω) := by
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let G : ℕ → Ω × ℂ → ℝ := fun n q => {z : ℂ | ‖z‖ < δ n}.indicator
    (fun z => ((max (ε n) ‖z‖) ^ (-γ*α) - (max (ε n/2) ‖z‖) ^ (-γ*α)) *
      ((ε n)^(γ^2/2) * Real.exp (γ*(H q.1 (ε n) z-H q.1 1 0)))) q.2
  have hG (n : ℕ) : Measurable (G n) := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε n) q.2) :=
      (hHm (ε n) (hε n)).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    have hw : Measurable (fun z : ℂ =>
        (max (ε n) ‖z‖) ^ (-γ*α) - (max (ε n/2) ‖z‖) ^ (-γ*α)) := by
      fun_prop
    exact (((hw.comp measurable_snd).mul
      (measurable_const.mul (measurable_const.mul (h1.sub h2)).exp)).indicator
      ((measurableSet_lt measurable_norm measurable_const).preimage measurable_snd))
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let F : ℕ → ContinuousPath ℂ × Ω → ℝ := fun n q =>
    ∫ z, G n (q.2,z) ∂(Measure.map (fun t => q.1 t) ν)
  have hF (n : ℕ) : Measurable (F n) := by
    have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
    have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
      heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h := (hG n).comp ((measurable_snd.comp measurable_fst).prodMk heval)
    have hm := h.stronglyMeasurable.integral_prod_right' (ν := ν)
    convert hm.measurable using 1
    funext q
    exact integral_map q.1.continuous.measurable.aemeasurable
      ((hG n).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine ⟨F, hF, ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh 0] with ω hω hrec b n
  rw [show F n (b, ω) = ∫ s in (0 : ℝ)..1, G n (ω, b s.toNNReal) from
    unit_path_occupation_integral_eq_time b (fun z => G n (ω,z))
      ((hG n).comp (measurable_const.prodMk measurable_id))]
  apply intervalIntegral.integral_congr
  intro s hs
  simp only [G, hω, Set.indicator_apply]
  split_ifs
  · rw [← hrec _ _ (hε n)]
    simp [ε]
  · rfl

/-- On a common field event, the correction is nonnegative and its
nonnegative time occupation equals the extended value of its real integral. -/
theorem ae_nonpositive_insertion_correction_lintegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∀ᵐ ω ∂P, ∀ b n,
      0 ≤ nonpositiveInsertionCorrection hcirc γ α (δ n) n (b, ω) ∧
      ENNReal.ofReal (nonpositiveInsertionCorrection hcirc γ α (δ n) n (b, ω)) =
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
            ((max ((2 : ℝ)⁻¹ ^ (n+1)) ‖z‖) ^ (-γ*α) -
             (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α)) *
            (((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ((2 : ℝ)⁻¹ ^ (n+1)) z)))
          (b s.toNNReal)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh 0] with ω hω hrec b n
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  let f : ℂ → ℝ := fun z => ((max ε ‖z‖) ^ (-γ*α) -
      (max (ε/2) ‖z‖) ^ (-γ*α)) *
    (ε^(γ^2/2) * Real.exp (γ*(H ω ε z-H ω 1 0)))
  have hf : Continuous f := by
    dsimp [f]
    have hw (r : ℝ) (hr : 0 < r) : Continuous (fun z : ℂ => (max r ‖z‖) ^ (-γ*α)) :=
      (continuous_const.max continuous_norm).rpow_const (fun _ => Or.inl (ne_of_gt (lt_max_of_lt_left hr)))
    exact ((hw ε hε).sub (hw (ε/2) (half_pos hε))).mul
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul ((hHc ω ε hε).sub continuous_const))))
  have hf0 (z : ℂ) : 0 ≤ f z := by
    dsimp [f]
    apply mul_nonneg _ (mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)
    apply sub_nonneg.mpr
    exact Real.rpow_le_rpow (le_of_lt (lt_max_of_lt_left (half_pos hε)))
      (max_le_max_right _ (by linarith)) hq
  have heq (z : ℂ) : {z : ℂ | ‖z‖ < δ n}.indicator f z =
      {z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
        ((max ε ‖z‖) ^ (-γ*α) - (max (ε/2) ‖z‖) ^ (-γ*α)) *
          (ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))) z := by
    simp only [f, hω, Set.indicator_apply]
    split_ifs
    · rw [← hrec ε z hε]
      simp
    · rfl
  have hint := inner_indicator_integrable_and_lintegral_eq b f hf hf0 (hδ n)
  have htime : nonpositiveInsertionCorrection hcirc γ α (δ n) n (b, ω) =
      ∫ z, {z : ℂ | ‖z‖ < δ n}.indicator f z ∂(Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := by
    rw [unit_path_occupation_integral_eq_time b _
      (hf.measurable.indicator (measurableSet_lt measurable_norm measurable_const))]
    apply intervalIntegral.integral_congr
    intro s hs
    exact (heq _).symm
  constructor
  · rw [htime]
    apply integral_nonneg
    intro z
    by_cases hz : ‖z‖ < δ n
    · simpa [hz] using hf0 z
    · simp [hz]
  · rw [htime, ← hint.2]
    apply lintegral_congr
    intro s
    rw [heq]

/-- The actual correction is product-integrable and obeys the annealed
power estimate. -/
theorem exists_integrable_nonpositive_insertion_corrections
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧ ∀ n,
      Integrable (nonpositiveInsertionCorrection hcirc γ α (δ n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫⁻ q, ENNReal.ofReal (nonpositiveInsertionCorrection hcirc γ α (δ n) n q)
        ∂((planarBrownianMotion x).prod P)) ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n+1)) ^ (-γ*α)) *
          ((ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (n+1))) ^ (1/2 : ℝ) * C) := by
  have := hh.isProbabilityMeasure
  obtain ⟨C, hC0, hC, hbound⟩ :=
    exists_annealed_nonpositive_insertion_correction_le hh x γ α hγ0 hγ2 hα
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_nonpositive_insertion_corrections hh γ α δ
  have hcae := ae_nonpositive_insertion_correction_lintegral hh hγ0.le hα δ hδ
  let μ := (planarBrownianMotion x).prod P
  have hFprod : ∀ᵐ q ∂μ, ∀ n, F n q =
      nonpositiveInsertionCorrection hcirc γ α (δ n) n q := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hFae] with q hq n
    exact hq q.1 n
  have hcprod : ∀ᵐ q ∂μ, ∀ n,
      0 ≤ nonpositiveInsertionCorrection hcirc γ α (δ n) n q ∧
      ENNReal.ofReal (nonpositiveInsertionCorrection hcirc γ α (δ n) n q) =
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
            ((max ((2 : ℝ)⁻¹ ^ (n+1)) ‖z‖) ^ (-γ*α) -
             (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α)) *
            (((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) ((2 : ℝ)⁻¹ ^ (n+1)) z)))
          (q.1 s.toNNReal)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hcae] with q hq n
    exact hq q.1 n
  refine ⟨C, hC0, hC, ?_⟩
  intro n
  have he : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hehalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hlin : (∫⁻ q, ENNReal.ofReal (nonpositiveInsertionCorrection hcirc γ α (δ n) n q) ∂μ) ≤
      ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n+1)) ^ (-γ*α)) *
        ((ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (n+1))) ^ (1/2 : ℝ) * C) := by
    calc
      _ = ∫⁻ q : ContinuousPath ℂ × Ω, (∫⁻ s in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ({z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
            ((max ((2 : ℝ)⁻¹ ^ (n+1)) ‖z‖) ^ (-γ*α) -
             (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α)) *
            (((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) ((2 : ℝ)⁻¹ ^ (n+1)) z)))
          (q.1 s.toNNReal))) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hcprod] with q hq
        exact (hq n).2
      _ = _ := (lintegral_prod_swap _).symm
      _ ≤ _ := hbound he hehalf (hδ n)
  have hm : AEStronglyMeasurable (nonpositiveInsertionCorrection hcirc γ α (δ n) n) μ := by
    apply (hFm n).aestronglyMeasurable.congr
    filter_upwards [hFprod] with q hq
    exact hq n
  have hnonneg : 0 ≤ᵐ[μ] nonpositiveInsertionCorrection hcirc γ α (δ n) n := by
    filter_upwards [hcprod] with q hq
    exact (hq n).1
  refine ⟨(lintegral_ofReal_ne_top_iff_integrable hm hnonneg).1 ?_, hlin⟩
  apply ne_of_lt (lt_of_le_of_lt hlin ?_)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hC)

/-- The annealed correction expectations have a summable geometric bound. -/
theorem exists_summable_annealed_nonpositive_insertion_corrections
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ B : ℕ → ℝ, Summable B ∧ (∀ n, 0 ≤ B n) ∧ ∀ n,
      Integrable (nonpositiveInsertionCorrection hcirc γ α (δ n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |nonpositiveInsertionCorrection hcirc γ α (δ n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ B n := by
  have := hh.isProbabilityMeasure
  obtain ⟨C, _, hC, hbound⟩ :=
    exists_integrable_nonpositive_insertion_corrections hh hγ0 hγ2 hα x δ hδ
  have hc := ae_nonpositive_insertion_correction_lintegral hh hγ0.le hα δ hδ
  let μ := (planarBrownianMotion x).prod P
  let B : ℕ → ℝ := fun n => C.toReal *
    Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * (1/2))
  have hB : Summable B := by
    exact (summable_nat_add_iff 1).2
      ((LatticeProb.Gauss.summable_exp_log_dyadicScale_mul (by norm_num : (0 : ℝ) < 1/2)).mul_left C.toReal)
  refine ⟨B, hB, fun n => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le, ?_⟩
  intro n
  have he : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have heone : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ0.le) hα
  have hweight : ((2 : ℝ)⁻¹ ^ (n+1)) ^ (-γ*α) ≤ 1 := Real.rpow_le_one he.le heone hq
  have hnonneg : 0 ≤ᵐ[μ] nonpositiveInsertionCorrection hcirc γ α (δ n) n := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hc] with q hq
    exact (hq q.1 n).1
  have hi := (hbound n).1
  have hlin := (hbound n).2
  have hrhs : ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n+1)) ^ (-γ*α)) *
      ((ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (n+1))) ^ (1/2 : ℝ) * C) < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hC)
  have hreal := ENNReal.toReal_mono hrhs.ne hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg, ENNReal.toReal_ofReal
    (integral_nonneg_of_ae hnonneg)] at hreal
  have hn : (∫ q, |nonpositiveInsertionCorrection hcirc γ α (δ n) n q| ∂μ) =
      ∫ q, nonpositiveInsertionCorrection hcirc γ α (δ n) n q ∂μ := by
    apply integral_congr_ae
    filter_upwards [hnonneg] with q hq
    exact abs_of_nonneg hq
  refine ⟨hi, ?_⟩
  rw [hn]
  calc
    _ ≤ _ := hreal
    _ = (((2 : ℝ)⁻¹ ^ (n+1)) ^ (-γ*α)) *
        ((((2 : ℝ)⁻¹ ^ (n+1)) ^ (1/2 : ℝ)) * C.toReal) := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
        ENNReal.toReal_ofReal he.le, ENNReal.toReal_ofReal (Real.rpow_nonneg he.le _)]
    _ ≤ 1 * ((((2 : ℝ)⁻¹ ^ (n+1)) ^ (1/2 : ℝ)) * C.toReal) := by
      gcongr
    _ = B n := by
      rw [Real.rpow_def_of_pos he]
      dsimp [B]
      ring

private theorem intervalIntegrable_inner_indicator (b : ContinuousPath ℂ)
    (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ) :
    IntervalIntegrable (fun s : ℝ => {z : ℂ | ‖z‖ < δ}.indicator f (b s.toNNReal))
      volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  have hp : Continuous (fun s : ℝ => b s.toNNReal) :=
    b.continuous.comp continuous_real_toNNReal
  have hi : IntegrableOn (Set.indicator ((fun s : ℝ => b s.toNNReal) ⁻¹' {z : ℂ | ‖z‖ < δ}) (fun s => f (b s.toNNReal))) (Ioc (0 : ℝ) 1) volume :=
    ((hf.comp hp).integrableOn_Icc.mono_set Ioc_subset_Icc_self).indicator
    ((measurableSet_lt measurable_norm measurable_const).preimage hp.measurable)
  convert hi using 1
  funext s
  by_cases hz : ‖b s.toNNReal‖ < δ <;> simp [hz]

/-- The actual inserted inner clock increment along a unit-time path. -/
noncomputable def nonpositiveInsertedInnerTimeIncrement {Ω : Type*}
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ : ℝ) (n : ℕ)
    (q : ContinuousPath ℂ × Ω) : ℝ :=
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (ε/2) z) -
    ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z))
      (q.1 s.toNNReal)

/-- The inserted increment equals the weighted zero-insertion increment less
the smoothing correction, simultaneously for all paths and scales. -/
theorem ae_nonpositive_inserted_inner_time_increment_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∀ᵐ ω ∂P, ∀ b n,
      nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n (b,ω) =
        weightedInnerZeroTimeIncrement hcirc γ
          ({z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
            (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))) n (b,ω) -
        nonpositiveInsertionCorrection hcirc γ α (δ n) n (b,ω) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh 0] with ω hω hrec b n
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  have he : 0 < ε := by dsimp [ε]; positivity
  have hehalf : ε ≤ 1/2 := by
    dsimp [ε]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let X : ℝ → ℂ → ℝ := fun r z => r^(γ^2/2) * Real.exp
    (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) r z)
  have hX (r : ℝ) (hr : 0 < r) : Continuous (X r) := by
    have hfun : X r = fun z => r^(γ^2/2) * Real.exp (γ*(H ω r z-H ω 1 0)) := by
      funext z
      dsimp [X]
      rw [hω, ← hrec r z hr]
      simp [← hω 1 0]
    rw [hfun]
    exact continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul ((hHc ω r hr).sub continuous_const)))
  have hw (r : ℝ) (hr : 0 < r) : Continuous (fun z : ℂ => (max r ‖z‖) ^ (-γ*α)) :=
    (continuous_const.max continuous_norm).rpow_const (fun _ => Or.inl (ne_of_gt (lt_max_of_lt_left hr)))
  let U : ℂ → ℝ := fun z => (max (ε/2) ‖z‖) ^ (-γ*α) * (X (ε/2) z - X ε z)
  let V : ℂ → ℝ := fun z => ((max ε ‖z‖) ^ (-γ*α) -
      (max (ε/2) ‖z‖) ^ (-γ*α)) * X ε z
  have hU : Continuous U := (hw (ε/2) (half_pos he)).mul ((hX _ (half_pos he)).sub (hX _ he))
  have hV : Continuous V := ((hw ε he).sub (hw (ε/2) (half_pos he))).mul (hX _ he)
  have hiU := intervalIntegrable_inner_indicator b U hU (δ n)
  have hiV := intervalIntegrable_inner_indicator b V hV (δ n)
  have hpoint (z : ℂ) : {z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
      (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z =
      {z : ℂ | ‖z‖ < δ n}.indicator U z - {z : ℂ | ‖z‖ < δ n}.indicator V z := by
    by_cases hz : ‖z‖ < δ n
    · simpa [Set.indicator_apply, hz, U, V, X] using (nonpositive_insertion_dyadic_density_increment (hcirc ω) γ α ε z hγ hα he hehalf
        (le_trans (le_of_lt hz) (hδ n))).2.2.2.2.2.2.1
    · simp [hz]
  change (∫ s in (0 : ℝ)..1, _ ) = (∫ s in (0 : ℝ)..1, _) - (∫ s in (0 : ℝ)..1, _)
  calc
    _ = ∫ s in (0 : ℝ)..1, ({z : ℂ | ‖z‖ < δ n}.indicator U (b s.toNNReal) -
        {z : ℂ | ‖z‖ < δ n}.indicator V (b s.toNNReal)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      exact hpoint _
    _ = (∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ n}.indicator U (b s.toNNReal)) -
        (∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ n}.indicator V (b s.toNNReal)) :=
      intervalIntegral.integral_sub hiU hiV
    _ = _ := by
      congr 1
      · apply intervalIntegral.integral_congr
        intro s hs
        simp only [U, X, Set.indicator_apply]
        split_ifs <;> simp [ε]

/-- Actual nonpositive inserted inner increments are integrable and their
annealed absolute expectations have summable bounds. -/
theorem exists_summable_annealed_nonpositive_inserted_inner_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧ ∀ n,
      Integrable (nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  have := hh.isProbabilityMeasure
  let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
    (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
  obtain ⟨A, hA, hA0, hinc⟩ :=
    exists_summable_annealed_nonpositive_weighted_increments hh hγ0 hγ2 hα x δ hδ
  obtain ⟨B, hB, hB0, hcorr⟩ :=
    exists_summable_annealed_nonpositive_insertion_corrections hh hγ0 hγ2 hα x δ hδ
  have heq := ae_nonpositive_inserted_inner_time_increment_eq hh hγ0.le hα δ hδ
  let μ := (planarBrownianMotion x).prod P
  have heqprod : ∀ᵐ q ∂μ, ∀ n,
      nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q =
        weightedInnerZeroTimeIncrement hcirc γ (g n) n q -
          nonpositiveInsertionCorrection hcirc γ α (δ n) n q := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae heq] with q hq n
    exact hq q.1 n
  refine ⟨fun n => A n + B n, hA.add hB, fun n => add_nonneg (hA0 n) (hB0 n), ?_⟩
  intro n
  have hW := (hinc n).1
  have hV := (hcorr n).1
  have hI : Integrable (nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n) μ := by
    apply (hW.sub hV).congr
    filter_upwards [heqprod] with q hq
    exact (hq n).symm
  refine ⟨hI, ?_⟩
  calc
    _ ≤ ∫ q, (|weightedInnerZeroTimeIncrement hcirc γ (g n) n q| +
        |nonpositiveInsertionCorrection hcirc γ α (δ n) n q|) ∂μ := by
      apply integral_mono_ae hI.abs (hW.abs.add hV.abs)
      filter_upwards [heqprod] with q hq
      rw [hq n]
      exact abs_sub _ _
    _ = (∫ q, |weightedInnerZeroTimeIncrement hcirc γ (g n) n q| ∂μ) +
        (∫ q, |nonpositiveInsertionCorrection hcirc γ α (δ n) n q| ∂μ) :=
      integral_add hW.abs hV.abs
    _ ≤ _ := add_le_add (hinc n).2 (hcorr n).2

/-- The actual inserted inner increments are almost surely absolutely summable,
and their expected tails vanish. -/
theorem exists_vanishing_annealed_nonpositive_inserted_inner_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      Filter.Tendsto (fun N => ∑' k, A (k+N)) Filter.atTop (nhds 0) ∧
      (∀ᵐ q ∂((planarBrownianMotion x).prod P),
        Summable (fun n => |nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q|)) ∧
      ∀ N, (∫ q, ∑' k, |nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ (k+N)) (k+N) q|
        ∂((planarBrownianMotion x).prod P)) ≤ ∑' k, A (k+N) := by
  obtain ⟨A, hA, hA0, hinc⟩ :=
    exists_summable_annealed_nonpositive_inserted_inner_increments hh hγ0 hγ2 hα x δ hδ
  let μ := (planarBrownianMotion x).prod P
  let f : ℕ → ContinuousPath ℂ × Ω → ℝ := fun n q =>
    |nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q|
  have hfi (n : ℕ) : Integrable (f n) μ := (hinc n).1.abs
  have hs : Summable (fun n => ∫ q, f n q ∂μ) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => abs_nonneg _))
      (fun n => (hinc n).2) hA
  refine ⟨A, hA, hA0, tendsto_sum_nat_add A, ?_, ?_⟩
  · exact LatticeProb.Gauss.ae_summable_of_summable_integral hfi
      (fun _ _ => abs_nonneg _) hs
  intro N
  have hsN : Summable (fun k => ∫ q, f (k+N) q ∂μ) := (summable_nat_add_iff N).2 hs
  have hAN : Summable (fun k => A (k+N)) := (summable_nat_add_iff N).2 hA
  have hnorm : Summable (fun k => ∫ q, ‖f (k+N) q‖ ∂μ) := by
    simpa only [f, Real.norm_eq_abs, abs_abs] using hsN
  have heq := (hasSum_integral_of_summable_integral_norm (fun k => hfi (k+N)) hnorm).tsum_eq
  change (∫ q, ∑' k, f (k+N) q ∂μ) ≤ ∑' k, A (k+N)
  rw [← heq]
  exact Summable.tsum_le_tsum (fun k => (hinc (k+N)).2) hsN hAN

end HarmonicBalls
