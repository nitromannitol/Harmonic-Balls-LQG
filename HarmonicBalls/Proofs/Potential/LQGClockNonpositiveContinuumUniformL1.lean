import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveUniformL1

/-! # Inner occupation bounds for nonpositive insertions

A uniform bound controls the inner occupation at every positive smoothing
radius and every Brownian starting point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The expected inner occupation for a nonpositive insertion obeys one
power bound uniformly in the Brownian starting point and smoothing radius. -/
theorem exists_uniform_lintegral_prod_brownian_inner_nonpositive_inserted_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {α ε δ : ℝ}, 0 ≤ γ → α ≤ 0 →
      0 < ε → ε ≤ 1/2 → 0 < δ → δ ≤ 1/2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤ (ENNReal.ofReal δ) ^ (1/2 : ℝ) * C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_lintegral_prod_brownian_inner_zero_le hh γ
  refine ⟨C, hC, ?_⟩
  intro x α ε δ hγ hα hε hεhalf hδ hδhalf
  have hcomp (ω : Ω) (z : ℂ) (hz : ‖z‖ < δ) :
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z ≤
      LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z := by
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
        Real.log (max ε ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hε)
    have hlogle : Real.log (max ε ‖z‖) ≤ 0 :=
      Real.log_nonpos (le_of_lt (lt_max_of_lt_left hε)) (max_le (by linarith) (by linarith))
    have hmul := mul_nonneg_of_nonpos_of_nonpos hα hlogle
    dsimp [LatticeProb.Gauss.fieldCircleAverage]
    rw [hlog]
    linarith
  calc
    _ ≤ (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) := by
      apply lintegral_mono
      intro q
      apply lintegral_mono
      intro s
      apply ENNReal.ofReal_le_ofReal
      simp only [Set.indicator_apply]
      split_ifs with hz
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left (hcomp q.1 _ hz) hγ))
          (Real.rpow_nonneg (le_of_lt hε) _)
      · exact le_rfl
    _ ≤ _ := hbound x hε hεhalf hδ hδhalf

/-- Almost-everywhere convergence of nonnegative functions and convergence
of their integrals imply convergence in L¹ along a countably generated filter. -/
theorem tendsto_integral_abs_sub_of_nonnegative_of_ae_tendsto
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {l : Filter ι} [l.IsCountablyGenerated] (f : ι → X → ℝ) (g : X → ℝ)
    (hf : ∀ᶠ i in l, Integrable (f i) μ) (hg : Integrable g μ)
    (hf0 : ∀ᶠ i in l, ∀ᵐ x ∂μ, 0 ≤ f i x) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 (g x)))
    (hmean : Tendsto (fun i => ∫ x, f i x ∂μ) l (𝓝 (∫ x, g x ∂μ))) :
    Tendsto (fun i => ∫ x, |f i x - g x| ∂μ) l (𝓝 0) := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (fun x => min (f i x) (g x)) μ := by
    filter_upwards [hf] with i hi
    exact (hi.aemeasurable.min hg.aemeasurable).aestronglyMeasurable
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖min (f i x) (g x)‖ ≤ g x := by
    filter_upwards [hf0] with i hi
    filter_upwards [hi, hg0] with x hix hx
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hix hx)]
    exact min_le_right _ _
  have hc : ∀ᵐ x ∂μ, Tendsto (fun i => min (f i x) (g x)) l (𝓝 (g x)) := by
    filter_upwards [hconv] with x hx
    simpa using hx.min (tendsto_const_nhds : Tendsto (fun _ : ι => g x) l (𝓝 (g x)))
  have hmin := tendsto_integral_filter_of_dominated_convergence g hm hb hg hc
  have heq : ∀ᶠ i in l, (∫ x, |f i x - g x| ∂μ) =
      (∫ x, f i x ∂μ) + (∫ x, g x ∂μ) - 2 * (∫ x, min (f i x) (g x) ∂μ) := by
    filter_upwards [hf] with i hi
    have hmi : Integrable (fun x => min (f i x) (g x)) μ := by
      convert hi.inf hg using 1
    have hp : (fun x => |f i x - g x|) =
        (fun x => f i x + g x - 2 * min (f i x) (g x)) := by
      funext x
      rcases le_total (f i x) (g x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    rw [hp]
    rw [integral_sub (f := fun x => f i x + g x) (g := fun x => 2 * min (f i x) (g x)) (hi.add hg) (hmi.const_mul 2)]
    rw [integral_add hi hg, integral_const_mul]
  have ht := (hmean.add (tendsto_const_nhds : Tendsto (fun _ : ι => ∫ x, g x ∂μ) l (𝓝 (∫ x, g x ∂μ)))).sub
    ((tendsto_const_nhds : Tendsto (fun _ : ι => (2 : ℝ)) l (𝓝 2)).mul hmin)
  have ht' : Tendsto (fun i => (∫ x, f i x ∂μ) + (∫ x, g x ∂μ) -
      2 * (∫ x, min (f i x) (g x) ∂μ)) l (𝓝 0) := by
    convert ht using 1; ring
  apply ht'.congr'
  filter_upwards [heq] with i hi
  exact hi.symm

/-- Field-averaged occupation in the closed ball equals the regularized insertion weight. -/
theorem lintegral_closedBall_inserted_density_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hδhalf : δ ≤ 1/2)
    (γ α : ℝ) (ν : Measure ℂ) [SFinite ν] :
    (∫⁻ ω, ∫⁻ z, {z : ℂ | ‖z‖ ≤ δ}.indicator
      (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂ν ∂P) =
    ∫⁻ z, {z : ℂ | ‖z‖ ≤ δ}.indicator
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) z ∂ν := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | ‖z‖ ≤ δ}
  have hA : MeasurableSet A := measurableSet_le measurable_norm measurable_const
  let F : Ω × ℂ → ℝ≥0∞ := fun q => A.indicator (fun z =>
    ENNReal.ofReal (ε ^ (γ^2/2) * Real.exp (γ*(H q.1 ε z - H q.1 1 0 -
      α*Real.log (max ε ‖z‖))))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hF : Measurable F := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).ennreal_ofReal
  have heq : ∀ᵐ ω ∂P, ∀ z, F (ω,z) = A.indicator (fun z =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec z
    dsimp [F]
    simp only [Set.indicator_apply]
    split_ifs with hz
    · rw [hω ε z, hω 1 0, hrec ε z hε]
    · rfl
  calc
    _ = ∫⁻ ω, ∫⁻ z, F (ω,z) ∂ν ∂P := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      apply lintegral_congr
      intro z
      exact (hω z).symm
    _ = ∫⁻ z, ∫⁻ ω, F (ω,z) ∂P ∂ν := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ A
      · have hz1 : ‖z‖ + ε ≤ 1 := by dsimp [A] at hz; linarith
        rw [Set.indicator_of_mem hz]
        calc
          (∫⁻ ω, F (ω,z) ∂P) = ∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) ∂P := by
              apply lintegral_congr_ae
              filter_upwards [heq] with ω hω
              rw [hω z, Set.indicator_of_mem hz]
          _ = _ := by rw [lintegral_inserted_clock_density_eq hh hε γ α hz1]
      · rw [Set.indicator_of_notMem hz]
        simp [F, Set.indicator_of_notMem hz]

/-- The product expectation of a closed-ball occupation equals the Brownian
occupation of the regularized insertion weight. -/
theorem lintegral_prod_closedBall_inserted_density_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (Q : Measure (ContinuousPath ℂ)) [SFinite Q] (ρ : Measure ℝ) [SFinite ρ]
    {ε δ : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hδhalf : δ ≤ 1/2)
    (γ α : ℝ) :
    (∫⁻ q : Ω × ContinuousPath ℂ, ∫⁻ s, ENNReal.ofReal
      ({z : ℂ | ‖z‖ ≤ δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)) ∂ρ
        ∂(P.prod Q)) =
    ∫⁻ b, ∫⁻ s, {z : ℂ | ‖z‖ ≤ δ}.indicator
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖))))
        (b s.toNNReal) ∂ρ ∂Q := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | ‖z‖ ≤ δ}
  have hA : MeasurableSet A := measurableSet_le measurable_norm measurable_const
  let G : Ω × ℂ → ℝ≥0∞ := fun q => A.indicator (fun z =>
    ENNReal.ofReal (ε ^ (γ^2/2) * Real.exp (γ * (H q.1 ε z - H q.1 1 0 -
      α * Real.log (max ε ‖z‖))))) q.2
  have hG : Measurable G := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
      (hHm ε hε).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).ennreal_ofReal
  have heq : ∀ᵐ ω ∂P, ∀ z, G (ω,z) = ENNReal.ofReal
      (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hr z
    dsimp [G]
    simp only [Set.indicator_apply]
    split_ifs with hz
    · rw [hω ε z, hω 1 0, hr ε z hε]
    · simp
  have hev : Measurable (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hjoint : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ =>
      G (p.1.1, p.1.2 p.2.toNNReal)) :=
    hG.comp (measurable_fst.fst.prodMk (hev.comp (measurable_fst.snd.prodMk measurable_snd)))
  have hrep : ∀ᵐ q ∂(P.prod Q), ∀ s : ℝ,
      G (q.1, q.2 s.toNNReal) = ENNReal.ofReal
        (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q)).ae heq] with q hq s
    exact hq _
  calc
    _ = ∫⁻ q : Ω × ContinuousPath ℂ, ∫⁻ s, G (q.1, q.2 s.toNNReal) ∂ρ ∂(P.prod Q) := by
      apply lintegral_congr_ae
      filter_upwards [hrep] with q hq
      exact lintegral_congr fun s => (hq s).symm
    _ = ∫⁻ b, ∫⁻ ω, ∫⁻ s, G (ω, b s.toNNReal) ∂ρ ∂P ∂Q :=
      lintegral_prod_symm _ hjoint.lintegral_prod_right'.aemeasurable
    _ = ∫⁻ b, ∫⁻ s, ∫⁻ ω, G (ω, b s.toNNReal) ∂P ∂ρ ∂Q := by
      apply lintegral_congr
      intro b
      apply lintegral_lintegral_swap
      exact (hG.comp (measurable_fst.prodMk
        (b.continuous.measurable.comp (continuous_real_toNNReal.measurable.comp measurable_snd)))).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro b
      apply lintegral_congr
      intro s
      by_cases hz : ‖b s.toNNReal‖ ≤ δ
      · rw [Set.indicator_of_mem (s := {z : ℂ | ‖z‖ ≤ δ}) hz]
        calc
          (∫⁻ ω, G (ω, b s.toNNReal) ∂P) = ∫⁻ ω, ENNReal.ofReal
              (ε ^ (γ ^ 2 / 2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                (hcirc ω) ε (b s.toNNReal))) ∂P := by
            apply lintegral_congr_ae
            filter_upwards [heq] with ω hω
            simpa [A, Set.indicator_apply, hz] using hω (b s.toNNReal)
          _ = _ := lintegral_inserted_clock_density_eq hh hε γ α (by linarith)
      · rw [Set.indicator_of_notMem (s := {z : ℂ | ‖z‖ ≤ δ}) hz]
        simp [G, A, Set.indicator_apply, hz]

/-- Closed-ball insertion weights converge in mean for any finite spatial measure. -/
theorem tendsto_lintegral_closedBall_insertion_weight
    (ν : Measure ℂ) [IsFiniteMeasure ν] {γ α : ℝ}
    (hγ : 0 ≤ γ) (hα : α ≤ 0) :
    Tendsto (fun ε : ℝ => ∫⁻ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) z ∂ν)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫⁻ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) z ∂ν)) := by
  have hp : 0 ≤ -(γ * α) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hγ hα)
  let f : ℝ → ℂ → ℝ≥0∞ := fun ε z => {z : ℂ | ‖z‖ ≤ 1/2}.indicator
    (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) z
  let g : ℂ → ℝ≥0∞ := fun z => {z : ℂ | ‖z‖ ≤ 1/2}.indicator
    (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) z
  have hA : MeasurableSet {z : ℂ | ‖z‖ ≤ 1/2} :=
    measurableSet_le measurable_norm measurable_const
  change Tendsto (fun ε => ∫⁻ z, f ε z ∂ν) _ (𝓝 (∫⁻ z, g z ∂ν))
  apply tendsto_lintegral_filter_of_dominated_convergence (fun _ => 1)
  · filter_upwards with ε
    exact (measurable_const.mul ((measurable_const.max measurable_norm).log)).exp.ennreal_ofReal.indicator hA
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))] with ε hε hεhalf
    filter_upwards with z
    change ε < (1/2 : ℝ) at hεhalf
    by_cases hz : ‖z‖ ≤ 1/2
    · have he : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
      have hb : max ε ‖z‖ ≤ 1 := max_le (by linarith) (by linarith)
      have hw : Real.exp (-(γ * α) * Real.log (max ε ‖z‖)) =
          (max ε ‖z‖) ^ (-(γ * α)) := by
        rw [Real.rpow_def_of_pos he]; congr 1; ring
      simp only [f, Set.indicator_of_mem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hz, hw]
      simpa using ENNReal.ofReal_le_ofReal (Real.rpow_le_one he.le hb hp)
    · simp only [f, Set.indicator_of_notMem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hz, zero_le_one]
  · simp
  · filter_upwards with z
    by_cases hz : ‖z‖ ≤ 1/2
    · have hx : Tendsto (fun ε : ℝ => max ε ‖z‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖z‖) := by
        simpa [max_eq_right (norm_nonneg z)] using
          ((tendsto_id.max tendsto_const_nhds).mono_left nhdsWithin_le_nhds :
            Tendsto (fun ε : ℝ => max ε ‖z‖) (𝓝[>] (0 : ℝ)) (𝓝 (max 0 ‖z‖)))
      have ht := ENNReal.continuous_ofReal.tendsto (‖z‖ ^ (-(γ * α))) |>.comp
        ((Real.continuous_rpow_const hp).tendsto ‖z‖ |>.comp hx)
      simp only [g, Set.indicator_of_mem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hz]
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have he : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
      simp only [f, Set.indicator_of_mem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hz]
      change ENNReal.ofReal ((max ε ‖z‖) ^ (-(γ * α))) =
        ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))
      rw [Real.rpow_def_of_pos he]
      congr 1
      ring
    · simp only [f, g, Set.indicator_of_notMem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hz]
      exact tendsto_const_nhds

/-- Product expectations of nonpositive inserted closed-ball occupations
converge as the smoothing radius tends to zero. -/
theorem tendsto_lintegral_prod_closedBall_nonpositive_inserted_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (Q : Measure (ContinuousPath ℂ)) [IsFiniteMeasure Q]
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] {γ α : ℝ} (hγ : 0 ≤ γ) (hα : α ≤ 0) :
    Tendsto (fun ε : ℝ => ∫⁻ q : Ω × ContinuousPath ℂ, ∫⁻ s, ENNReal.ofReal
      ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)) ∂ρ ∂(P.prod Q))
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫⁻ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator
        (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) z
        ∂((Q.prod ρ).map (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal)))) := by
  let ev : ContinuousPath ℂ × ℝ → ℂ := fun p => p.1 p.2.toNNReal
  have hev : Measurable ev :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  let ν := (Q.prod ρ).map ev
  let : IsFiniteMeasure ν := (Q.prod ρ).isFiniteMeasure_map ev
  have ht := tendsto_lintegral_closedBall_insertion_weight ν hγ hα
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1/2 by norm_num))] with ε hε hεhalf
  have hw : Measurable (fun z : ℂ => {z : ℂ | ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) z) :=
    (measurable_const.mul ((measurable_const.max measurable_norm).log)).exp.ennreal_ofReal.indicator
      (measurableSet_le measurable_norm measurable_const)
  rw [lintegral_prod_closedBall_inserted_density_eq hh Q ρ hε (le_of_lt hεhalf) le_rfl γ α]
  change (∫⁻ z, _ ∂((Q.prod ρ).map ev)) = _
  rw [lintegral_map hw hev]
  simpa only [Function.comp_apply, ev] using
    (lintegral_prod _ (hw.comp hev).aemeasurable)

end HarmonicBalls
