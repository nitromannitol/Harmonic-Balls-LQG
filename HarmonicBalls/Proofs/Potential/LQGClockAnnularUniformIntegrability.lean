import HarmonicBalls.Proofs.Potential.LQGClockAnnularTimeIdentity
import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.Prob.UniformIntegrableDominated

/-! # Uniform integrability of bounded-time annular clocks

The inserted-field annular clocks are uniformly integrable in the Brownian law
for almost every field and each fixed starting point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter Set
open scoped NNReal ENNReal Topology

namespace HarmonicBalls

/-- A spatial density integrated along a bounded-time annular occupation measure. -/
noncomputable def stoppedAnnularClock (f : ℂ → ℝ) (δ : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) : ℝ :=
  ∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f z
    ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))

/-- A continuous spatial density gives an integrable bounded-time annular clock. -/
theorem integrable_stoppedAnnularClock_of_continuous (x : ℂ) (f : ℂ → ℝ)
    (hf : Continuous f) (δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    Integrable (stoppedAnnularClock f δ τ) (planarBrownianMotion x) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let g : ℂ → ℝ := A.indicator f
  have hg : Measurable g := hf.measurable.indicator hA
  let G : Unit × ℂ → ℝ := fun q => g q.2
  have hG : Measurable G := hg.comp measurable_snd
  have hpath : Measurable (stoppedAnnularClock f δ τ) := by
    have hm := (measurable_stopped_path_integral G hG τ hτ).comp
      (measurable_id.prodMk (measurable_const : Measurable (fun _ : ContinuousPath ℂ => ())))
    exact hm
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  have hgK : ∀ z, ‖g z‖ ≤ max K 0 := by
    intro z
    by_cases hz : z ∈ A
    · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
      rw [show g z = f z from Set.indicator_of_mem hz _]
      exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, norm_zero]
      exact le_max_right K 0
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  apply (integrable_const (max K 0)).mono' hpath.aestronglyMeasurable
  filter_upwards with b
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (τ b)))
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  have hμ : μ ≤ ρ := Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  calc
    ‖stoppedAnnularClock f δ τ b‖ ≤ ∫ _ : ℂ, max K 0 ∂μ :=
      by simpa [stoppedAnnularClock, g, A, μ, ν, integral_const, smul_eq_mul, mul_comm] using
        (norm_integral_le_of_norm_le_const (μ := μ) (f := g)
          (Filter.Eventually.of_forall hgK))
    _ ≤ ∫ _ : ℂ, max K 0 ∂ρ :=
      integral_mono_measure hμ (Filter.Eventually.of_forall fun _ => le_max_right K 0)
        (integrable_const _)
    _ = max K 0 := by simp

private theorem integrable_annular_density (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ)
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f) μ := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  apply (integrable_const (max K 0)).mono' (hf.measurable.indicator hA).aestronglyMeasurable
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    rw [show A.indicator f z = f z from Set.indicator_of_mem hz _]
    exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
  · rw [show A.indicator f z = 0 from Set.indicator_of_notMem hz _, norm_zero]
    exact le_max_right K 0

/-- An annular increment before averaging over the field. -/
noncomputable def annularIncrementSample {Ω : Type*} [MeasurableSpace Ω]
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (ω : Ω) : ℝ :=
  ∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
    ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))

/-- The annular increment admits a jointly measurable modification. -/
theorem exists_measurable_annularIncrementSample
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ b, F (b, ω) = annularIncrementSample hcirc γ α δ ε τ b ω := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let G : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε/2) z-H q.1 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε/2) q.2) :=
    (hHm (ε/2) (half_pos hε)).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hG : Measurable G := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  refine ⟨_, measurable_stopped_path_integral G hG τ hτ, ?_⟩
  filter_upwards [hHae] with ω hω b
  apply integral_congr_ae
  filter_upwards with z
  simp only [G, A, hω]

/-- For each path, a small-scale annular increment is integrable in the field. -/
theorem integrable_stopped_annular_increment_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    Integrable (fun ω => ∫ z,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
      ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))) P := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let g : ℂ → ℝ := A.indicator (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖)))
  have hδ : 0 < δ := hε.trans_le hεδ
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let f : ℂ → ℝ := fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))
  have hgm : Measurable g := hf.measurable.indicator hA
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.continuousOn
  have hgK : ∀ z, |g z| ≤ max K 0 := by
    intro z
    by_cases hz : z ∈ A
    · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
      rw [show g z = f z from Set.indicator_of_mem hz _, abs_of_pos (Real.exp_pos _)]
      exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, abs_zero]
      exact le_max_right K 0
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (τ b)))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun t => b t) ν) hμ
  have hgi : Integrable g μ := by
    apply (integrable_const (max K 0)).mono' hgm.aestronglyMeasurable
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgK z
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1 := by
    intro z hz
    have hzA : z ∈ A := by
      by_contra hn
      exact hz (Set.indicator_of_notMem hn _)
    linarith [hzA.2]
  have hi := hh.integrable_integral_increment hε zero_lt_one μ hgm hgi hgs γ
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hδε : ε ≤ ‖z‖ := hεδ.trans hz.1
    have hhalf : ε/2 ≤ ‖z‖ := by linarith
    rw [show A.indicator _ z = _ from Set.indicator_of_mem hz _,
      show g z = _ from Set.indicator_of_mem hz _, max_eq_right hz.1,
      max_eq_right hδε, max_eq_right hhalf]
    have heq (r : ℝ) : γ * (hcirc ω r z - hcirc ω 1 0 - α * Real.log ‖z‖) =
        -γ*α*Real.log ‖z‖ + γ*(hcirc ω r z-hcirc ω 1 0) := by ring
    rw [heq (ε/2), heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show A.indicator _ z = _ from Set.indicator_of_notMem hz _,
      show g z = _ from Set.indicator_of_notMem hz _, zero_mul]

/-- At sufficiently small scales the joint annular increment is integrable. -/
theorem exists_integrable_annularIncrementSample
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
      Integrable F ((planarBrownianMotion x).prod P) ∧
      ∀ᵐ ω ∂P, ∀ b, F (b, ω) = annularIncrementSample hcirc γ α δ ε τ b ω := by
  have := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_annularIncrementSample hh hε γ α δ τ hτ
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_stopped_annular_inserted_increment_annealed_le hh hγ0 hγ2 α x
      (hε.trans_le hεδ) τ hτ
  have hfield : ∀ b, Integrable (fun ω => F (b, ω)) P := by
    intro b
    apply (integrable_stopped_annular_increment_field hh hε hεhalf hεδ γ α τ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have heq : (fun b => ∫ ω, ‖F (b, ω)‖ ∂P) =
      stoppedAnnularIncrement P hcirc γ α δ ε τ := by
    funext b
    unfold stoppedAnnularIncrement
    apply integral_congr_ae
    filter_upwards [hFae] with ω hω
    rw [hω b]
    rfl
  refine ⟨F, hFm, ?_, hFae⟩
  apply (integrable_prod_iff hFm.aestronglyMeasurable).2
  refine ⟨Filter.Eventually.of_forall hfield, ?_⟩
  rw [heq]
  exact (hb ε hε hεhalf hεδ).1

/-- The annealed annular increment estimates are summable at dyadic scales. -/
theorem summable_brownian_stopped_annular_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    Summable (fun k : ℕ => ∫ b, stoppedAnnularIncrement P hcirc γ α δ
      (dyadicScale k) τ b ∂(planarBrownianMotion x)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_stopped_annular_inserted_increment_annealed_le hh hγ0 hγ2 α x hδ τ hτ
  let A : ℝ := ((Real.exp (γ^2*Real.log 2)-1) *
    (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2
  let c : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hsum : Summable (fun k : ℕ => A * Real.exp (Real.log (dyadicScale k) * c) +
      2*M*Real.exp (Real.log (dyadicScale k) * e)) := by
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hc
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul he
    exact (h1.mul_left A).add (h2.mul_left (2*M))
  have hlim : Tendsto dyadicScale atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ k in atTop, dyadicScale k < min (1/2) δ :=
    hlim.eventually (Iio_mem_nhds (lt_min (by norm_num) hδ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  apply (summable_nat_add_iff N).1
  apply Summable.of_nonneg_of_le (fun k => integral_nonneg (fun b => integral_nonneg (fun ω => abs_nonneg _)))
    _ ((summable_nat_add_iff N).2 hsum)
  intro k
  have hk := hN (k + N) (by omega)
  exact (hb _ (dyadicScale_pos _) (le_of_lt (lt_of_lt_of_le hk (min_le_left _ _)))
    (le_of_lt (lt_of_lt_of_le hk (min_le_right _ _)))).2

/-- The Brownian L¹ norms of small-scale annular increments are almost surely summable. -/
theorem ae_summable_brownian_stopped_annular_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    ∃ N : ℕ, ∀ᵐ ω ∂P, Summable (fun k : ℕ =>
      ∫ b, ‖annularIncrementSample hcirc γ α δ (dyadicScale (k + N)) τ b ω‖
        ∂(planarBrownianMotion x)) := by
  have := hh.isProbabilityMeasure
  have hlim : Tendsto dyadicScale atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hlim.eventually
    (Iio_mem_nhds (lt_min (by norm_num : (0 : ℝ) < 1/2) hδ)))
  have hsmall (k : ℕ) : dyadicScale (k+N) ≤ 1/2 ∧ dyadicScale (k+N) ≤ δ := by
    have h := hN (k+N) (by omega)
    exact ⟨(lt_of_lt_of_le h (min_le_left _ _)).le,
      (lt_of_lt_of_le h (min_le_right _ _)).le⟩
  have hex (k : ℕ) := exists_integrable_annularIncrementSample hh hγ0 hγ2 α x
    (dyadicScale_pos (k+N)) (hsmall k).1 (hsmall k).2 τ hτ
  let F : ℕ → ContinuousPath ℂ × Ω → ℝ := fun k => Classical.choose (hex k)
  have hFm (k : ℕ) : Measurable (F k) := (Classical.choose_spec (hex k)).1
  have hFi (k : ℕ) : Integrable (F k) ((planarBrownianMotion x).prod P) :=
    (Classical.choose_spec (hex k)).2.1
  have hFae (k : ℕ) : ∀ᵐ ω ∂P, ∀ b, F k (b,ω) =
      annularIncrementSample hcirc γ α δ (dyadicScale (k+N)) τ b ω :=
    (Classical.choose_spec (hex k)).2.2
  let g : ℕ → Ω → ℝ := fun k ω => ∫ b, ‖F k (b,ω)‖ ∂(planarBrownianMotion x)
  have hg (k : ℕ) : Integrable (g k) P := (hFi k).integral_norm_prod_right
  have hg0 (k : ℕ) (ω : Ω) : 0 ≤ g k ω := integral_nonneg fun _ => norm_nonneg _
  have hmean (k : ℕ) : (∫ ω, g k ω ∂P) =
      ∫ b, stoppedAnnularIncrement P hcirc γ α δ (dyadicScale (k+N)) τ b
        ∂(planarBrownianMotion x) := by
    rw [show (∫ ω, g k ω ∂P) = ∫ b, ∫ ω, ‖F k (b,ω)‖ ∂P
      ∂(planarBrownianMotion x) from (integral_integral_swap (hFi k).norm).symm]
    apply integral_congr_ae
    filter_upwards with b
    unfold stoppedAnnularIncrement
    apply integral_congr_ae
    filter_upwards [hFae k] with ω hω
    rw [hω b]
    rfl
  have hsum : Summable (fun k => ∫ ω, g k ω ∂P) := by
    simp_rw [hmean]
    exact (summable_nat_add_iff N).2
      (summable_brownian_stopped_annular_increment hh hγ0 hγ2 α x hδ τ hτ)
  have hfinite : (∫⁻ ω, ∑' k, ‖g k ω‖ₑ ∂P) ≠ ∞ := by
    rw [lintegral_tsum (fun k => (hg k).aestronglyMeasurable.enorm)]
    have heq (k : ℕ) : (∫⁻ ω, ‖g k ω‖ₑ ∂P) = ENNReal.ofReal (∫ ω, g k ω ∂P) := by
      calc
        _ = ∫⁻ ω, ENNReal.ofReal (g k ω) ∂P := by
          apply lintegral_congr
          intro ω
          exact Real.enorm_eq_ofReal (hg0 k ω)
        _ = _ := (ofReal_integral_eq_lintegral_ofReal (hg k)
          (Filter.Eventually.of_forall (hg0 k))).symm
    simp_rw [heq, ← ENNReal.ofReal_tsum_of_nonneg
      (fun k => integral_nonneg (hg0 k)) hsum]
    exact ENNReal.ofReal_ne_top
  have hmeas : AEMeasurable (fun ω => ∑' k, ‖g k ω‖ₑ) P :=
    AEMeasurable.tsum fun k => (hg k).aestronglyMeasurable.enorm
  refine ⟨N, ?_⟩
  filter_upwards [ae_lt_top' hmeas hfinite, ae_all_iff.mpr hFae] with ω hω hFω
  have hs : Summable (fun k => ‖g k ω‖) := tsum_enorm_ne_top_iff_summable_norm.mp hω.ne
  apply hs.congr
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (hg0 k ω)]
  unfold g
  apply integral_congr_ae
  filter_upwards with b
  rw [hFω k b]


private theorem continuous_inserted_density (hcirc : ℝ → ℂ → ℝ) (γ α r : ℝ)
    (hr : 0 < r) (hc : Continuous (hcirc r))
    (hrec : ∀ z, hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) =
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z) :
    Continuous (fun z => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z)) := by
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α hcirc r z) =
      fun z => hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) := by
    funext z
    exact (hrec z).symm
  have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α hcirc r z) := by
    rw [heq]
    exact (hc.sub continuous_const).sub
      (continuous_const.mul ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left hr).ne')))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))

private theorem annular_clock_increment_eq
    (hcirc : ℝ → ℂ → ℝ) (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0)
    (hcont : ∀ r, 0 < r → Continuous (hcirc r))
    (hrec : ∀ r z, 0 < r → hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) =
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z)
    (k : ℕ) (b : ContinuousPath ℂ) :
    stoppedAnnularClock (fun z => (dyadicScale (k+1))^(γ^2/2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc (dyadicScale (k+1)) z)) δ τ b -
    stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc (dyadicScale k) z)) δ τ b =
    annularIncrementSample (fun _ : Unit => hcirc) γ α δ (dyadicScale k) τ b () := by
  let D : ℕ → ℂ → ℝ := fun k z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α hcirc (dyadicScale k) z)
  have hD (j : ℕ) : Continuous (D j) := continuous_inserted_density hcirc γ α _
    (dyadicScale_pos j) (hcont _ (dyadicScale_pos j)) (fun z => hrec _ z (dyadicScale_pos j))
  have hscale : dyadicScale (k+1) = dyadicScale k / 2 := by
    simp only [dyadicScale, pow_succ]
    ring
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (τ b)))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun t => b t) ν) hμ
  change (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (D (k+1)) z ∂μ) -
    (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (D k) z ∂μ) = _
  rw [← integral_sub (integrable_annular_density _ (hD (k+1)) δ μ)
    (integrable_annular_density _ (hD k) δ μ)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Set.indicator_apply]
  split_ifs
  · dsimp [D]
    rw [hscale, ← hrec _ z (half_pos (dyadicScale_pos k)),
      ← hrec _ z (dyadicScale_pos k)]
  · ring

/-- The inserted-field annular dyadic clocks are Brownian uniformly integrable. -/
theorem ae_uniformIntegrable_stopped_annular_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    ∀ᵐ ω ∂P, UniformIntegrable (fun k : ℕ => fun b =>
      stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
        δ τ b) 1 (planarBrownianMotion x) := by
  obtain ⟨N, hsum⟩ := ae_summable_brownian_stopped_annular_increment hh hγ0 hγ2 α x hδ τ hτ
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hsum, hcont, ae_recentered_inserted_circle_average hh α] with ω hsum hcont hrec
  apply LatticeProb.Prob.uniformIntegrable_of_summable_integral_norm_sub
  · intro k
    apply integrable_stoppedAnnularClock_of_continuous
    · exact continuous_inserted_density (hcirc ω) γ α _ (dyadicScale_pos k)
        (hcont _ (dyadicScale_pos k)) (fun z => hrec _ z (dyadicScale_pos k))
    · exact hτ
  · have hs : Summable (fun k : ℕ => ∫ b,
        ‖annularIncrementSample hcirc γ α δ (dyadicScale k) τ b ω‖
          ∂(planarBrownianMotion x)) := by
      exact (summable_nat_add_iff N).1 hsum
    apply hs.congr
    intro k
    apply integral_congr_ae
    filter_upwards with b
    exact congrArg norm (annular_clock_increment_eq (hcirc ω) γ α δ τ hcont hrec k b).symm

/-- An annular occupation integral is the corresponding bounded-time integral. -/
theorem stoppedAnnularClock_eq_time_integral (f : ℂ → ℝ) (hf : Measurable f)
    (δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    stoppedAnnularClock f δ τ b =
      ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) (τ b) : ℝ),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let g : ℂ → ℝ := A.indicator f
  have hg : Measurable g := hf.indicator hA
  change (∫ z, g z ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
    (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))) = _
  rw [integral_map b.continuous.measurable.aemeasurable hg.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => g (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hg.comp b.continuous.measurable).aestronglyMeasurable]
  simp only [NNReal.coe_one]
  rw [intervalIntegral.integral_of_le
    (show (0 : ℝ) ≤ min (1 : ℝ) (τ b : ℝ) from le_min zero_le_one (τ b).coe_nonneg),
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨hs, h0, h1⟩
    exact ⟨h0, h1, (Real.toNNReal_le_iff_le_coe).mp hs⟩
  · rintro ⟨h0, h1, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, h1⟩

/-- For each fixed starting point, the actual bounded-time annular inserted-field
clock integrals are uniformly integrable for almost every field. -/
theorem ae_uniformIntegrable_annular_clock_time_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) (hτbound : ∀ b, τ b ≤ 1) :
    ∀ᵐ ω ∂P, UniformIntegrable (fun k : ℕ => fun b =>
      ∫ s in (0 : ℝ)..(τ b : ℝ),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
          (b s.toNNReal)) 1 (planarBrownianMotion x) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [ae_uniformIntegrable_stopped_annular_clock hh hγ0 hγ2 α x hδ τ hτ,
    hcont, ae_recentered_inserted_circle_average hh α] with ω hui hcont hrec
  apply hui.ae_eq
  intro k
  apply Filter.Eventually.of_forall
  intro b
  have hf := continuous_inserted_density (hcirc ω) γ α _ (dyadicScale_pos k)
    (hcont _ (dyadicScale_pos k)) (fun z => hrec _ z (dyadicScale_pos k))
  dsimp only
  rw [stoppedAnnularClock_eq_time_integral _ hf.measurable δ τ b]
  simp only [NNReal.coe_one]
  rw [min_eq_right (show (τ b : ℝ) ≤ 1 by exact_mod_cast hτbound b)]


end HarmonicBalls
