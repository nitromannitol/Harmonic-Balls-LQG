import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveContinuumConvergence

/-! # Continuum uniform L¹ convergence of nonpositive half-disc clocks

A uniform bound controls the inner occupation at every positive smoothing
radius and every Brownian starting point. First moments of the closed
half-disc occupations converge as the smoothing radius tends to zero, and the
actual closed half-disc clocks converge in uniform-time product-law L¹ on every
finite horizon, over all positive radii, to the jointly measurable dyadic limit.
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
    convert ht using 1; ring_nf
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
      ring_nf
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


/-- The closed half-disc clocks at all positive smoothing radii have jointly
measurable field, path and time versions with continuous, nonnegative and
monotone time paths, which agree with the clocks off one field-null set. -/
theorem exists_measurable_halfDisc_inserted_clock_prod_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∃ M : ℝ → (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ,
      (∀ ε, 0 < ε → Measurable (M ε)) ∧
      (∀ ε, 0 < ε → ∀ p, Continuous (fun t => M ε (p, t))) ∧
      (∀ ε, 0 < ε → ∀ p t, 0 ≤ M ε (p, t)) ∧
      (∀ ε, 0 < ε → ∀ p, Monotone (fun t => M ε (p, t))) ∧
      ∀ᵐ ω ∂P, ∀ ε, 0 < ε → ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
        M ε ((ω, b), t) = (∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)) ∧
        ENNReal.ofReal (M ε ((ω, b), t)) = ∫⁻ s in Ioc (0 : ℝ) (t : ℝ),
          ENNReal.ofReal ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)) := by
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hB : MeasurableSet {z : ℂ | ‖z‖ ≤ 1/2} := measurableSet_le measurable_norm measurable_const
  have hII (g : ℂ → ℝ) (hg : Continuous g) (b : ContinuousPath ℂ) (a c : ℝ) :
      IntervalIntegrable (fun s : ℝ => {z : ℂ | ‖z‖ ≤ 1/2}.indicator g (b s.toNNReal))
        volume a c := by
    have h := intervalIntegrable_annular_density g hg 0 b a c
    simp only [norm_nonneg, true_and] at h
    exact h
  let f (ε : ℝ) (ω : Ω) (z : ℂ) : ℝ := ε ^ (γ ^ 2 / 2) * Real.exp
    (γ * (H ω ε z - H ω 1 0 - α * Real.log (max ε ‖z‖)))
  have hfc (ε : ℝ) (hε : 0 < ε) (ω : Ω) : Continuous (f ε ω) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (((hHc ω ε hε).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne'))))))
  have hf0 (ε : ℝ) (hε : 0 < ε) (ω : Ω) (z : ℂ) : 0 ≤ f ε ω z :=
    mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
  have hind0 (ε : ℝ) (hε : 0 < ε) (ω : Ω) (w : ℂ) :
      0 ≤ {z : ℂ | ‖z‖ ≤ 1/2}.indicator (f ε ω) w :=
    Set.indicator_nonneg (fun z _ => hf0 ε hε ω z) w
  have hJ (ε : ℝ) (hε : 0 < ε) :
      Measurable (fun q : Ω × ℂ => {z : ℂ | ‖z‖ ≤ 1/2}.indicator (f ε q.1) q.2) := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) := (hHm ε hε).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    apply Measurable.indicator _ (hB.preimage measurable_snd)
    exact measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp
  have heval : Measurable (fun q : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      q.1.1.2 q.2.toNNReal) :=
    (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  let S : Set (((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ (q.1.2 : ℝ)}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd
      (measurable_coe_nnreal_real.comp (measurable_snd.comp measurable_fst)))
  let Q (ε : ℝ) : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ → ℝ := fun q =>
    S.indicator (fun q => {z : ℂ | ‖z‖ ≤ 1/2}.indicator (f ε q.1.1.1) (q.1.1.2 q.2.toNNReal)) q
  have hQ (ε : ℝ) (hε : 0 < ε) : Measurable (Q ε) :=
    ((hJ ε hε).comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      heval)).indicator hS
  let M (ε : ℝ) : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ := fun q => ∫ s, Q ε (q, s)
  have hMm (ε : ℝ) (hε : 0 < ε) : Measurable (M ε) :=
    (hQ ε hε).stronglyMeasurable.integral_prod_right'.measurable
  have hMeq (ε : ℝ) (ω : Ω) (b : ContinuousPath ℂ) (t : ℝ≥0) :
      M ε ((ω, b), t) = ∫ s in (0 : ℝ)..(t : ℝ),
        {z : ℂ | ‖z‖ ≤ 1/2}.indicator (f ε ω) (b s.toNNReal) := by
    rw [intervalIntegral.integral_of_le t.coe_nonneg, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with s
    simp only [Q, S, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc]
  have hfeq : ∀ᵐ ω ∂P, ∀ ε, 0 < ε → f ε ω = fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec ε hε
    funext z
    simp only [f, hω ε z, hω 1 0, hrec ε z hε]
  refine ⟨M, hMm, ?_, ?_, ?_, ?_⟩
  · intro ε hε p
    have heq : (fun t => M ε (p, t)) = fun t : ℝ≥0 =>
        ∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | ‖z‖ ≤ 1/2}.indicator (f ε p.1) (p.2 s.toNNReal) :=
      funext (hMeq ε p.1 p.2)
    rw [heq]
    exact (intervalIntegral.continuous_primitive (hII _ (hfc ε hε p.1) p.2) 0).comp
      continuous_subtype_val
  · rintro ε hε ⟨ω, b⟩ t
    rw [hMeq ε ω b t]
    exact intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (fun s => hind0 ε hε ω _)
  · rintro ε hε ⟨ω, b⟩ s t hst
    show M ε ((ω, b), s) ≤ M ε ((ω, b), t)
    rw [hMeq ε ω b s, hMeq ε ω b t]
    exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg (NNReal.coe_le_coe.mpr hst)
      (Filter.Eventually.of_forall (fun u => hind0 ε hε ω _)) (hII _ (hfc ε hε ω) b 0 t)
  · filter_upwards [hfeq] with ω hω ε hε b t
    have hlin : ENNReal.ofReal (M ε ((ω, b), t)) = ∫⁻ s in Ioc (0 : ℝ) (t : ℝ),
        ENNReal.ofReal ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (f ε ω) (b s.toNNReal)) := by
      rw [hMeq ε ω b t, intervalIntegral.integral_of_le t.coe_nonneg]
      exact ofReal_integral_eq_lintegral_ofReal (hII _ (hfc ε hε ω) b 0 t).1
        (Filter.Eventually.of_forall (fun u => hind0 ε hε ω _))
    refine ⟨?_, ?_⟩
    · rw [hMeq ε ω b t, hω ε hε]
    · rw [hlin, hω ε hε]

/-- The product expectation of a nonpositive inserted closed half-disc
occupation is at most the product of the masses of the time and path
measures. -/
theorem lintegral_prod_closedBall_nonpositive_inserted_density_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (Q : Measure (ContinuousPath ℂ)) [SFinite Q] (ρ : Measure ℝ) [SFinite ρ]
    {ε γ α : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hγ : 0 ≤ γ) (hα : α ≤ 0) :
    (∫⁻ q : Ω × ContinuousPath ℂ, ∫⁻ s, ENNReal.ofReal
      ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)) ∂ρ
        ∂(P.prod Q)) ≤ ρ univ * Q univ := by
  have hp : 0 ≤ -(γ * α) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hγ hα)
  have hpt (w : ℂ) : {z : ℂ | ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) w ≤ 1 := by
    by_cases hw : ‖w‖ ≤ 1/2
    · rw [Set.indicator_of_mem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hw]
      apply ENNReal.ofReal_le_one.mpr
      apply Real.exp_le_one_iff.mpr
      apply mul_nonpos_of_nonneg_of_nonpos hp
      exact Real.log_nonpos (le_of_lt (lt_max_of_lt_left hε)) (max_le (by linarith) (by linarith))
    · rw [Set.indicator_of_notMem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hw]
      exact zero_le_one
  rw [lintegral_prod_closedBall_inserted_density_eq hh Q ρ hε hεhalf le_rfl γ α]
  calc
    _ ≤ ∫⁻ _b : ContinuousPath ℂ, ∫⁻ _s : ℝ, (1 : ℝ≥0∞) ∂ρ ∂Q := by
      apply lintegral_mono
      intro b
      apply lintegral_mono
      intro s
      exact hpt _
    _ = ρ univ * Q univ := by rw [lintegral_one, lintegral_const]

/-- The closed half-disc integral of a nonnegative power of the norm is finite
for a finite measure. -/
theorem lintegral_closedBall_norm_rpow_ne_top (ν : Measure ℂ) [IsFiniteMeasure ν]
    {γ α : ℝ} (hγ : 0 ≤ γ) (hα : α ≤ 0) :
    (∫⁻ z, {z : ℂ | ‖z‖ ≤ 1/2}.indicator
      (fun z => ENNReal.ofReal (‖z‖ ^ (-(γ * α)))) z ∂ν) ≠ ⊤ := by
  have hp : 0 ≤ -(γ * α) := neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hγ hα)
  refine ne_top_of_le_ne_top (measure_ne_top ν Set.univ) ?_
  rw [← lintegral_one]
  apply lintegral_mono
  intro z
  by_cases hz : ‖z‖ ≤ 1/2
  · rw [Set.indicator_of_mem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hz]
    exact ENNReal.ofReal_le_one.mpr (Real.rpow_le_one (norm_nonneg z) (by linarith) hp)
  · rw [Set.indicator_of_notMem (s := {z : ℂ | ‖z‖ ≤ 1/2}) hz]
    exact zero_le_one

/-- Product expectations of nonpositive inserted closed half-disc occupations
have a finite limit as the smoothing radius tends to zero. -/
theorem exists_tendsto_lintegral_prod_closedBall_nonpositive_inserted_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (Q : Measure (ContinuousPath ℂ)) [IsFiniteMeasure Q]
    (ρ : Measure ℝ) [IsFiniteMeasure ρ] {γ α : ℝ} (hγ : 0 ≤ γ) (hα : α ≤ 0) :
    ∃ m : ℝ≥0∞, m ≠ ⊤ ∧
      Tendsto (fun ε : ℝ => ∫⁻ q : Ω × ContinuousPath ℂ, ∫⁻ s, ENNReal.ofReal
        ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)) ∂ρ
          ∂(P.prod Q)) (𝓝[>] (0 : ℝ)) (𝓝 m) := by
  have : IsFiniteMeasure ((Q.prod ρ).map (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal)) :=
    (Q.prod ρ).isFiniteMeasure_map _
  exact ⟨_, lintegral_closedBall_norm_rpow_ne_top
    ((Q.prod ρ).map (fun p : ContinuousPath ℂ × ℝ => p.1 p.2.toNNReal)) hγ hα,
    tendsto_lintegral_prod_closedBall_nonpositive_inserted_density hh Q ρ hγ hα⟩

/-- Nonnegative functions bounded by an integrable function plus errors with
vanishing integrals, and tending to zero almost everywhere, have integrals
tending to zero along a countably generated filter. -/
theorem tendsto_integral_of_nonneg_le_add_of_ae_tendsto_zero
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X}
    {l : Filter ι} [l.IsCountablyGenerated] (h e : ι → X → ℝ) (g : X → ℝ)
    (hi : ∀ᶠ i in l, Integrable (h i) μ) (hg : Integrable g μ)
    (he : ∀ᶠ i in l, Integrable (e i) μ)
    (h0 : ∀ᶠ i in l, ∀ᵐ x ∂μ, 0 ≤ h i x) (he0 : ∀ᶠ i in l, ∀ᵐ x ∂μ, 0 ≤ e i x)
    (hle : ∀ᶠ i in l, ∀ᵐ x ∂μ, h i x ≤ g x + e i x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i => h i x) l (𝓝 0))
    (hemean : Tendsto (fun i => ∫ x, e i x ∂μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ x, h i x ∂μ) l (𝓝 0) := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (fun x => min (h i x) |g x|) μ := by
    filter_upwards [hi] with i hi
    exact (hi.aemeasurable.min hg.abs.aemeasurable).aestronglyMeasurable
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖min (h i x) |g x|‖ ≤ |g x| := by
    filter_upwards [h0] with i hi
    filter_upwards [hi] with x hix
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min hix (abs_nonneg _))]
    exact min_le_right _ _
  have hc : ∀ᵐ x ∂μ, Tendsto (fun i => min (h i x) |g x|) l (𝓝 0) := by
    filter_upwards [hconv] with x hx
    have ht := hx.min (tendsto_const_nhds : Tendsto (fun _ : ι => |g x|) l (𝓝 |g x|))
    rwa [min_eq_left (abs_nonneg (g x))] at ht
  have hmin : Tendsto (fun i => ∫ x, min (h i x) |g x| ∂μ) l (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (fun x => |g x|) hm hb hg.abs hc
    rwa [integral_zero] at ht
  have hupper : ∀ᶠ i in l, ∫ x, h i x ∂μ ≤ ∫ x, min (h i x) |g x| ∂μ + ∫ x, e i x ∂μ := by
    filter_upwards [hi, he, he0, hle] with i hii hei he0i hlei
    have hmi : Integrable (fun x => min (h i x) |g x|) μ := by
      convert hii.inf hg.abs using 1
    rw [← integral_add hmi hei]
    apply integral_mono_ae hii (hmi.add hei)
    filter_upwards [hlei, he0i] with x hx hx0
    have hg' := le_abs_self (g x)
    show h i x ≤ min (h i x) |g x| + e i x
    rcases le_total (h i x) |g x| with hc | hc
    · rw [min_eq_left hc]
      linarith
    · rw [min_eq_right hc]
      linarith
  have hlow : ∀ᶠ i in l, 0 ≤ ∫ x, h i x ∂μ := by
    filter_upwards [h0] with i hi
    exact integral_nonneg_of_ae hi
  have hsum : Tendsto (fun i => ∫ x, min (h i x) |g x| ∂μ + ∫ x, e i x ∂μ) l (𝓝 0) := by
    have ht := hmin.add hemean
    rwa [add_zero] at ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum hlow hupper

/-- Two reals are equal when each is approximated arbitrarily well by one of two
equal reals. -/
theorem eq_of_forall_abs_sub_lt_of_eq {a b : ℝ}
    (h : ∀ η : ℝ, 0 < η → ∃ u v : ℝ, u = v ∧ |u - a| < η ∧ |v - b| < η) : a = b := by
  apply eq_of_forall_dist_le
  intro η hη
  obtain ⟨u, v, huv, hu, hv⟩ := h (η / 2) (half_pos hη)
  rw [huv] at hu
  rw [Real.dist_eq]
  calc
    |a - b| ≤ |a - v| + |v - b| := abs_sub_le a v b
    _ = |v - a| + |v - b| := by rw [abs_sub_comm a v]
    _ ≤ η / 2 + η / 2 := add_le_add hu.le hv.le
    _ = η := add_halves η

/-- At each fixed Brownian start, the nonpositive inserted closed half-disc
clocks converge in uniform-time product-law L¹ on every finite horizon as the
positive smoothing radius tends to zero, to the same jointly measurable limit
as the dyadic clocks. -/
theorem exists_measurable_nonpositive_halfDisc_clock_uniformL1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (hα : α ≤ 0) :
    ∃ F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable F ∧
      (∀ p, Continuous (fun t => F (p,t)) ∧ (∀ t, 0 ≤ F (p,t)) ∧
        Monotone (fun t => F (p,t))) ∧
      (∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F (p,t)| < η) ∧
      (∀ T : ℝ≥0, ∃ (A : ℕ → (Ω × ContinuousPath ℂ) → C(Icc (0 : ℝ) (T : ℝ), ℝ))
          (B : (Ω × ContinuousPath ℂ) → C(Icc (0 : ℝ) (T : ℝ), ℝ)),
        (∀ j, Measurable (A j)) ∧ Measurable B ∧
        (∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ j t,
          A j p t = ∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) ∧
        (∀ p t, B p t = F (p,(t : ℝ).toNNReal)) ∧
        (∀ j, Integrable (fun p => ‖A j p - B p‖) (P.prod (planarBrownianMotion x))) ∧
        Tendsto (fun j => ∫ p, ‖A j p - B p‖ ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0)) ∧
      (∀ᵐ p ∂(P.prod (planarBrownianMotion x)),
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ r : ℝ, 0 < r → r < ρ → ∀ t : ℝ≥0, t ≤ T →
            |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
              r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                (hcirc p.1) r z)) (p.2 s.toNNReal)) - F (p,t)| < η) ∧
      ∀ T : ℝ≥0,
        ∃ (A : Set.Ioc (0 : ℝ) (1/2) → Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ))
          (B : Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ)),
          (∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ r t,
            A r p t = ∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
              (r : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                (hcirc p.1) r z)) (p.2 s.toNNReal)) ∧
          (∀ p t, B p t = F (p, (t : ℝ).toNNReal)) ∧ Measurable B ∧
          (∀ r, Measurable (A r)) ∧
          (∀ r, Integrable (fun p => ‖A r p - B p‖) (P.prod (planarBrownianMotion x))) ∧
          Tendsto (fun r => ∫ p, ‖A r p - B p‖ ∂(P.prod (planarBrownianMotion x)))
            (Filter.comap (fun r : Set.Ioc (0 : ℝ) (1/2) => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := P.prod (planarBrownianMotion x)
  obtain ⟨F, hFm, hFr, hFlim, hFL1⟩ :=
    exists_measurable_uniform_L1_limit_nonpositive_halfDiscClock hh x hγ hγ2 hα
  obtain ⟨L, -, -, hL⟩ :=
    exists_measurable_nonpositive_halfDisc_clock_continuum_limit hh x hγ hγ2 hα
  have hFL : ∀ᵐ p ∂μ, ∀ t, F (p,t) = L (p,t) := by
    filter_upwards [hFlim, hL] with p hp hpL t
    apply eq_of_forall_abs_sub_lt_of_eq
    intro η hη
    obtain ⟨j, hj1, hj2⟩ := ((hp t η hη).and (hpL.1 t η hη)).exists
    exact ⟨_, _, by simp only [norm_nonneg, true_and]; rfl, hj1 t le_rfl, hj2 t le_rfl⟩
  have hFcont : ∀ᵐ p ∂μ, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, 0 < r → r < ρ → ∀ t : ℝ≥0, t ≤ T →
        |(∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
          r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
            (hcirc p.1) r z)) (p.2 s.toNNReal)) - F (p,t)| < η := by
    filter_upwards [hL, hFL] with p hp hpF
    intro T η hη
    obtain ⟨ρ, hρ, hρb⟩ := hp.2 T η hη
    refine ⟨ρ, hρ, fun r hr hrρ t ht => ?_⟩
    rw [hpF t]
    exact hρb r hr hrρ t ht
  refine ⟨F, hFm, hFr, hFlim, hFL1, hFcont, ?_⟩
  intro T
  obtain ⟨M, hMm, hMc, hM0, hMmono, hMae⟩ :=
    exists_measurable_halfDisc_inserted_clock_prod_time hh γ α
  have hMprod : ∀ᵐ p ∂μ, ∀ ε, 0 < ε → ∀ t : ℝ≥0,
      M ε (p, t) = (∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)) ∧
      ENNReal.ofReal (M ε (p, t)) = ∫⁻ s in Ioc (0 : ℝ) (t : ℝ),
        ENNReal.ofReal ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae hMae] with p hp ε hε t
    exact hp ε hε p.2 t
  let A : Set.Ioc (0 : ℝ) (1/2) → Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) :=
    fun r p => ⟨fun t => M r (p, (t : ℝ).toNNReal),
      (hMc r r.property.1 p).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  let B : Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun p =>
    ⟨fun t => F (p, (t : ℝ).toNNReal),
      (hFr p).1.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hAm (r : Set.Ioc (0 : ℝ) (1/2)) : Measurable (A r) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm r r.property.1).comp (measurable_id.prodMk measurable_const)
  have hBm : Measurable B := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hFm.comp (measurable_id.prodMk measurable_const)
  have hAeq : ∀ᵐ p ∂μ, ∀ (r : Set.Ioc (0 : ℝ) (1/2)) (t : Icc (0 : ℝ) (T : ℝ)),
      A r p t = ∫ s in (0 : ℝ)..(t : ℝ), {z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z =>
        (r : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
          (hcirc p.1) r z)) (p.2 s.toNNReal) := by
    filter_upwards [hMprod] with p hp r t
    simpa only [A, ContinuousMap.coe_mk, Real.toNNReal_of_nonneg t.property.1,
      NNReal.coe_mk] using (hp r r.property.1 ((t : ℝ).toNNReal)).1
  have hAnorm (r : Set.Ioc (0 : ℝ) (1/2)) (p : Ω × ContinuousPath ℂ) : ‖A r p‖ ≤ M r (p,T) := by
    apply (ContinuousMap.norm_le (A r p) (hM0 r r.property.1 p T)).2
    intro t
    have ht : (t : ℝ).toNNReal ≤ T :=
      NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
    change ‖M r (p, (t : ℝ).toNNReal)‖ ≤ M r (p,T)
    rw [Real.norm_eq_abs, abs_of_nonneg (hM0 r r.property.1 p _)]
    exact hMmono r r.property.1 p ht
  have hBnorm (p : Ω × ContinuousPath ℂ) : ‖B p‖ ≤ F (p,T) := by
    apply (ContinuousMap.norm_le (B p) ((hFr p).2.1 T)).2
    intro t
    have ht : (t : ℝ).toNNReal ≤ T :=
      NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
    change ‖F (p, (t : ℝ).toNNReal)‖ ≤ F (p,T)
    rw [Real.norm_eq_abs, abs_of_nonneg ((hFr p).2.1 _)]
    exact (hFr p).2.2 ht
  have hbound (r : Set.Ioc (0 : ℝ) (1/2)) (p : Ω × ContinuousPath ℂ) :
      ‖A r p - B p‖ ≤ 2 * F (p,T) + |M r (p,T) - F (p,T)| := by
    have h1 := norm_sub_le (A r p) (B p)
    have h2 := hAnorm r p
    have h3 := hBnorm p
    have h4 := le_abs_self (M r (p,T) - F (p,T))
    linarith
  have hMTm (e : ℝ) (he : 0 < e) : Measurable (fun p => M e (p,T)) :=
    (hMm e he).comp (measurable_id.prodMk measurable_const)
  have hFTm : Measurable (fun p => F (p,T)) := hFm.comp (measurable_id.prodMk measurable_const)
  have hIeq (e : ℝ) (he : 0 < e) : (∫⁻ p, ENNReal.ofReal (M e (p,T)) ∂μ) =
      ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal
        ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z => e ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) e z)) (q.2 s.toNNReal))) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hMprod] with p hp
    exact (hp e he T).2
  have ha (e : ℝ) (he : 0 < e) (he2 : e ≤ 1/2) : Integrable (fun p => M e (p,T)) μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable (f := fun p => M e (p,T))
      (hMTm e he).aestronglyMeasurable (ae_of_all _ (fun p => hM0 e he p T))).mp
    rw [hIeq e he]
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (measure_ne_top (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) univ)
      (measure_ne_top (planarBrownianMotion x) univ))
      (lintegral_prod_closedBall_nonpositive_inserted_density_le hh (planarBrownianMotion x)
        (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) he he2 hγ.le hα)
  have hmeanEq (e : ℝ) (he : 0 < e) : ∫ p, M e (p,T) ∂μ =
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal
        ({z : ℂ | ‖z‖ ≤ 1/2}.indicator (fun z => e ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) e z)) (q.2 s.toNNReal))) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun p => M e (p,T))
      (ae_of_all _ (fun p => hM0 e he p T)) (hMTm e he).aestronglyMeasurable, hIeq e he]
  obtain ⟨m, hmtop, hIlim⟩ := exists_tendsto_lintegral_prod_closedBall_nonpositive_inserted_density
    hh (planarBrownianMotion x) (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) hγ.le hα
  obtain ⟨AD, BD, -, -, hADeq, hBDeq, hADi, hADt⟩ := hFL1 T
  obtain ⟨Tpt, hTpt⟩ : ∃ u : Icc (0 : ℝ) (T : ℝ), (u : ℝ) = T := ⟨⟨T, T.coe_nonneg, le_rfl⟩, rfl⟩
  have hBDT (p : Ω × ContinuousPath ℂ) : BD p Tpt = F (p,T) := by
    rw [hBDeq p Tpt, hTpt, Real.toNNReal_coe]
  have hADT : ∀ᵐ p ∂μ, ∀ j : ℕ, AD j p Tpt = M (dyadicScale (j+1)) (p,T) := by
    filter_upwards [hADeq, hMprod] with p hp hq j
    rw [hp j Tpt, (hq _ (dyadicScale_pos (j+1)) T).1, hTpt]
    simp only [norm_nonneg, true_and]
  have hdle (j : ℕ) : dyadicScale (j+1) ≤ 1/2 := by
    show (2 : ℝ)⁻¹ ^ (j+1) ≤ 1/2
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hFTi : Integrable (fun p => F (p,T)) μ := by
    refine ((ha _ (dyadicScale_pos (0+1)) (hdle 0)).add (hADi 0)).mono'
      hFTm.aestronglyMeasurable ?_
    filter_upwards [hADT] with p hp
    have h1 := (AD 0 p - BD p).norm_coe_le_norm Tpt
    rw [ContinuousMap.sub_apply, hp 0, hBDT p, Real.norm_eq_abs] at h1
    change ‖F (p,T)‖ ≤ M (dyadicScale (0+1)) (p,T) + ‖AD 0 p - BD p‖
    rw [Real.norm_eq_abs, abs_of_nonneg ((hFr p).2.1 T)]
    have h2 := neg_abs_le (M (dyadicScale (0+1)) (p,T) - F (p,T))
    linarith
  have hdy : Tendsto (fun j : ℕ => ∫ p, M (dyadicScale (j+1)) (p,T) ∂μ) atTop
      (𝓝 (∫ p, F (p,T) ∂μ)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hADt
    show ‖∫ p, M (dyadicScale (j+1)) (p,T) ∂μ - ∫ p, F (p,T) ∂μ‖ ≤ ∫ p, ‖AD j p - BD p‖ ∂μ
    rw [← integral_sub (ha _ (dyadicScale_pos (j+1)) (hdle j)) hFTi]
    refine (norm_integral_le_integral_norm _).trans
      (integral_mono_ae ((ha _ (dyadicScale_pos (j+1)) (hdle j)).sub hFTi).norm (hADi j) ?_)
    filter_upwards [hADT] with p hp
    have h1 := (AD j p - BD p).norm_coe_le_norm Tpt
    rw [ContinuousMap.sub_apply, hp j, hBDT p] at h1
    exact h1
  have he0 : Tendsto (fun j : ℕ => dyadicScale (j+1)) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall (fun j => dyadicScale_pos (j+1))⟩
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1)).comp (tendsto_add_atTop_nat 1)
  have hdy' : Tendsto (fun j : ℕ => ∫ p, M (dyadicScale (j+1)) (p,T) ∂μ) atTop
      (𝓝 m.toReal) :=
    ((ENNReal.tendsto_toReal hmtop).comp (hIlim.comp he0)).congr
      (fun j => (hmeanEq _ (dyadicScale_pos (j+1))).symm)
  have hEF : ∫ p, F (p,T) ∂μ = m.toReal := tendsto_nhds_unique hdy hdy'
  have hT1 : Tendsto (fun r : Set.Ioc (0 : ℝ) (1/2) => ∫ p, |M r (p,T) - F (p,T)| ∂μ)
      (Filter.comap (fun r : Set.Ioc (0 : ℝ) (1/2) => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 0) := by
    apply tendsto_integral_abs_sub_of_nonnegative_of_ae_tendsto
    · exact Eventually.of_forall (fun r => ha r r.property.1 r.property.2)
    · exact hFTi
    · exact Eventually.of_forall (fun r => ae_of_all _ (fun p => hM0 r r.property.1 p T))
    · exact ae_of_all _ (fun p => (hFr p).2.1 T)
    · filter_upwards [hFcont, hMprod] with p hp hq
      rw [Metric.tendsto_nhds]
      intro η hη
      obtain ⟨ρ, hρ, hρb⟩ := hp T η hη
      have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ρ := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hρ)
      filter_upwards [tendsto_comap.eventually hev] with r hr
      show dist (M r (p,T)) (F (p,T)) < η
      rw [Real.dist_eq, (hq r r.property.1 T).1]
      exact hρb r r.property.1 hr T le_rfl
    · rw [hEF]
      exact ((ENNReal.tendsto_toReal hmtop).comp (hIlim.comp tendsto_comap)).congr
        (fun r => (hmeanEq r r.property.1).symm)
  have hAi (r : Set.Ioc (0 : ℝ) (1/2)) : Integrable (fun p => ‖A r p - B p‖) μ := by
    refine ((ha r r.property.1 r.property.2).add hFTi).mono'
      ((hAm r).sub hBm).norm.aestronglyMeasurable (ae_of_all _ (fun p => ?_))
    change ‖‖A r p - B p‖‖ ≤ M r (p,T) + F (p,T)
    rw [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hAnorm r p) (hBnorm p))
  have hlim : Tendsto (fun r : Set.Ioc (0 : ℝ) (1/2) => ∫ p, ‖A r p - B p‖ ∂μ)
      (Filter.comap (fun r : Set.Ioc (0 : ℝ) (1/2) => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 0) := by
    refine tendsto_integral_of_nonneg_le_add_of_ae_tendsto_zero (fun r p => ‖A r p - B p‖)
      (fun r p => |M r (p,T) - F (p,T)|) (fun p => 2 * F (p,T))
      (Eventually.of_forall hAi) (hFTi.const_mul 2)
      (Eventually.of_forall (fun r => ((ha r r.property.1 r.property.2).sub hFTi).abs))
      (Eventually.of_forall (fun r => ae_of_all _ (fun p => norm_nonneg _)))
      (Eventually.of_forall (fun r => ae_of_all _ (fun p => abs_nonneg _)))
      (Eventually.of_forall (fun r => ae_of_all _ (fun p => hbound r p))) ?_ hT1
    filter_upwards [hFcont, hAeq] with p hp hpa
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨ρ, hρ, hρb⟩ := hp T (η / 2) (half_pos hη)
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < ρ := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hρ)
    filter_upwards [tendsto_comap.eventually hev] with r hr
    have hle : ‖A r p - B p‖ ≤ η / 2 := by
      apply (ContinuousMap.norm_le (A r p - B p) (le_of_lt (half_pos hη))).2
      intro t
      have ht : (t : ℝ).toNNReal ≤ T :=
        NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
      have h := (hρb r r.property.1 hr ((t : ℝ).toNNReal) ht).le
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, B, ContinuousMap.coe_mk,
        hpa r t, Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using h
    show dist ‖A r p - B p‖ 0 < η
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
    exact lt_of_le_of_lt hle (half_lt_self hη)
  exact ⟨A, B, hAeq, fun _ _ => rfl, hBm, hAm, hAi, hlim⟩

end HarmonicBalls
