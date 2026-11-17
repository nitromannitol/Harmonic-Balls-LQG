import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInnerOccupation

/-! # Product measurability of inner clock increments

Zero-insertion inner time increments admit jointly measurable versions.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

private theorem measurable_unit_path_integral_inner {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω × ℂ → ℝ) (hF : Measurable F) :
    Measurable (fun q : ContinuousPath ℂ × Ω =>
      ∫ z, F (q.2, z) ∂(Measure.map (fun t => q.1 t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
    heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => F (q.1.2, q.1.1 q.2)) :=
    hF.comp ((measurable_snd.comp measurable_fst).prodMk heval)
  have hm := hG.stronglyMeasurable.integral_prod_right' (ν := ν)
  convert hm.measurable using 1
  funext q
  exact integral_map q.1.continuous.measurable.aemeasurable
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- Inner zero-insertion time increments have jointly measurable versions,
with one field event valid for every continuous path and index. -/
theorem exists_measurable_inner_zero_time_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) (δ : ℕ → ℝ) :
    ∃ F : ℕ → ContinuousPath ℂ × Ω → ℝ, (∀ n, Measurable (F n)) ∧
      ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (n : ℕ),
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        F n (b, ω) = ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))
            (b s.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let G : ℕ → Ω × ℂ → ℝ := fun n q => {z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
    (ε n/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε n/2) z-H q.1 1 0)) -
    (ε n)^(γ^2/2) * Real.exp (γ*(H q.1 (ε n) z-H q.1 1 0))) q.2
  have hG (n : ℕ) : Measurable (G n) := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε n/2) q.2) :=
      (hHm (ε n/2) (half_pos (hε n))).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 (ε n) q.2) :=
      (hHm (ε n) (hε n)).comp measurable_swap
    have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    apply Measurable.indicator _ ((measurableSet_lt measurable_norm measurable_const).preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul (h1.sub h3)).exp).sub
      (measurable_const.mul (measurable_const.mul (h2.sub h3)).exp)
  refine ⟨fun n q => ∫ z, G n (q.2,z) ∂(Measure.map (fun t => q.1 t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))),
    fun n => measurable_unit_path_integral_inner (G n) (hG n), ?_⟩
  filter_upwards [hHae, ae_inner_zero_increment_occupation_eq_time hh γ] with ω hω ht b n
  change (∫ z, G n (ω,z) ∂(Measure.map (fun t => b t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))) = _
  change _ = ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
    (ε n/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (ε n/2) z) -
    (ε n)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (ε n) z))
      (b s.toNNReal)
  rw [← ht (ε n) (δ n) (hε n) b]
  apply integral_congr_ae
  filter_upwards with z
  simp only [G, hω, Set.indicator_apply]
  split_ifs <;> simp

/-- Each actual inner time increment is measurable modulo any s-finite
path-field product law. -/
theorem aemeasurable_inner_zero_time_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure (ContinuousPath ℂ)) [SFinite ν] (γ : ℝ) (δ : ℕ → ℝ) (n : ℕ) :
    AEMeasurable (fun q : ContinuousPath ℂ × Ω =>
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) ε z))
          (q.1 s.toNNReal)) (ν.prod P) := by
  have := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_inner_zero_time_increments hh γ δ
  apply (hFm n).aemeasurable.congr
  filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae hFae] with q hq
  exact hq q.1 n

/-- The actual zero-insertion increment inside a deterministic ball. -/
noncomputable def innerZeroTimeIncrement {Ω : Type*}
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ δ : ℝ) (n : ℕ)
    (q : ContinuousPath ℂ × Ω) : ℝ :=
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) (ε/2) z) -
    ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) ε z))
      (q.1 s.toNNReal)

/-- The absolute annealed expectations of the actual inner increments are
bounded by a summable deterministic sequence. -/
theorem exists_summable_annealed_inner_zero_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      ∀ n, Integrable (innerZeroTimeIncrement hcirc γ (δ n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |innerZeroTimeIncrement hcirc γ (δ n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  have := hh.isProbabilityMeasure
  obtain ⟨R, hRi, hRs, _, hR0, hRbound⟩ :=
    exists_integrable_summable_inner_increment_envelope hh hγ0 hγ2 x
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_inner_zero_time_increments hh γ δ
  have hFtime : ∀ᵐ ω ∂P, ∀ b n,
      F n (b,ω) = innerZeroTimeIncrement hcirc γ (δ n) n (b,ω) := by
    filter_upwards [hFae] with ω hω b n
    exact hω b n
  have hFspatial : ∀ᵐ ω ∂P, ∀ b n,
      F n (b,ω) = ∫ z, ({z : ℂ | ‖z‖ < δ n}.indicator (fun _ => (1 : ℝ)) z) *
        ((((2 : ℝ)⁻¹ ^ (n+1))/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (((2 : ℝ)⁻¹ ^ (n+1))/2) z-hcirc ω 1 0)) -
        ((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ*(hcirc ω ((2 : ℝ)⁻¹ ^ (n+1)) z-hcirc ω 1 0)))
        ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1)))) := by
    filter_upwards [hFtime, ae_inner_zero_increment_occupation_eq_time hh γ] with ω hf ht b n
    rw [hf b n]
    exact (ht _ _ (by positivity) b).symm
  refine ⟨fun n => ∫ b, R n b ∂(planarBrownianMotion x), hRs,
    fun n => integral_nonneg (hR0 n), ?_⟩
  intro n
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F n (b,ω)) P := by
    apply (integrable_inner_increment_field hh hpos hhalf (hδ n) γ b).congr
    filter_upwards [hFspatial] with ω hω
    exact (hω b n).symm
  have hbound : ∀ᵐ b ∂(planarBrownianMotion x), (∫ ω, ‖F n (b,ω)‖ ∂P) ≤ R n b := by
    filter_upwards [hRbound] with b hb
    have heq : (∫ ω, ‖F n (b,ω)‖ ∂P) = ∫ ω, |∫ z,
        ({z : ℂ | ‖z‖ < δ n}.indicator (fun _ => (1 : ℝ)) z) *
        ((((2 : ℝ)⁻¹ ^ (n+1))/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (((2 : ℝ)⁻¹ ^ (n+1))/2) z-hcirc ω 1 0)) -
        ((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ*(hcirc ω ((2 : ℝ)⁻¹ ^ (n+1)) z-hcirc ω 1 0)))
        ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))| ∂P := by
      apply integral_congr_ae
      filter_upwards [hFspatial] with ω hω
      rw [hω b n, Real.norm_eq_abs]
    rw [heq]
    exact hb (δ n) (hδ n) _ le_rfl n
  have hsec : Integrable (fun b => ∫ ω, ‖F n (b,ω)‖ ∂P) (planarBrownianMotion x) := by
    apply (hRi n).mono' ((hFm n).stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards [hbound] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb
  have hFi : Integrable (F n) ((planarBrownianMotion x).prod P) :=
    (integrable_prod_iff (hFm n).aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hfield, hsec⟩
  have hprod : ∀ᵐ q ∂((planarBrownianMotion x).prod P),
      F n q = innerZeroTimeIncrement hcirc γ (δ n) n q := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hFtime] with q hq
    exact hq q.1 n
  refine ⟨hFi.congr hprod, ?_⟩
  calc
    _ = ∫ q, |F n q| ∂((planarBrownianMotion x).prod P) := by
      apply integral_congr_ae
      filter_upwards [hprod] with q hq
      rw [hq]
    _ = ∫ b, ∫ ω, ‖F n (b,ω)‖ ∂P ∂(planarBrownianMotion x) := by
      simpa only [Real.norm_eq_abs] using integral_prod (fun q => |F n q|) hFi.abs
    _ ≤ _ := integral_mono_ae hsec (hRi n) hbound

/-- The annealed expected tail of actual inner dyadic increments has a
summable deterministic bound that tends to zero. -/
theorem exists_vanishing_annealed_inner_zero_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      Filter.Tendsto (fun N => ∑' k, A (k+N)) Filter.atTop (nhds 0) ∧
      (∀ᵐ q ∂((planarBrownianMotion x).prod P),
        Summable (fun n => |innerZeroTimeIncrement hcirc γ (δ n) n q|)) ∧
      ∀ N, (∫ q, ∑' k, |innerZeroTimeIncrement hcirc γ (δ (k+N)) (k+N) q|
        ∂((planarBrownianMotion x).prod P)) ≤ ∑' k, A (k+N) := by
  obtain ⟨A, hA, hA0, hinc⟩ :=
    exists_summable_annealed_inner_zero_increments hh hγ0 hγ2 x δ hδ
  let μ := (planarBrownianMotion x).prod P
  let f : ℕ → ContinuousPath ℂ × Ω → ℝ := fun n q =>
    |innerZeroTimeIncrement hcirc γ (δ n) n q|
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
