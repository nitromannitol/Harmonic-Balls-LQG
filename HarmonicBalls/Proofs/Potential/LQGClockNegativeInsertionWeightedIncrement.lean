import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInnerAnnealedTail
import HarmonicBalls.Proofs.Potential.LQGClockNegativeInsertionAnnealedTail

/-! # Weighted inner clock increments

Bounded spatial weights preserve summable annealed increment estimates.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A geometric envelope controls all bounded inner-ball weights and is integrable
in Brownian motion with summable expectations. -/
theorem exists_integrable_summable_weighted_inner_increment_envelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∃ R : ℕ → ContinuousPath ℂ → ℝ,
      (∀ n, Integrable (R n) (planarBrownianMotion x)) ∧
      Summable (fun n => ∫ b, R n b ∂(planarBrownianMotion x)) ∧
      (∀ b, Summable (fun n => R n b)) ∧
      (∀ n b, 0 ≤ R n b) ∧
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ g : ℂ → ℝ, Measurable g →
      (∀ z, |g z| ≤ 1) → (∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2) → ∀ μ : Measure ℂ,
      μ ≤ Measure.map (fun t => b t) ν → ∀ n : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        (∫ ω, |∫ z, g z *
          ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤ R n b := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hb⟩ :=
    ae_brownian_field_submeasure_weighted_increment_le_riesz_energy hh hγ0 hγ2 x
  let u : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let v : ℝ := (θ-γ)^2/2
  let A : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(unitOccupationRieszEnergy d b * 2^d)+1)/2
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  have hA (b : ContinuousPath ℂ) : 0 ≤ A b := by
    dsimp [A]
    have he : 0 ≤ Real.exp (γ^2*Real.log 2)-1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    have hE : 0 ≤ unitOccupationRieszEnergy d b := ENNReal.toReal_nonneg
    positivity
  let R : ℕ → ContinuousPath ℂ → ℝ := fun n b =>
    A b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
      2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
  refine ⟨R, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have hE : Integrable (unitOccupationRieszEnergy d) (planarBrownianMotion x) :=
      integrable_unitOccupationRieszEnergy x hd0 hd2
    dsimp [R, A]
    fun_prop
  · have hE : Integrable (unitOccupationRieszEnergy d) (planarBrownianMotion x) :=
      integrable_unitOccupationRieszEnergy x hd0 hd2
    have hAi : Integrable A (planarBrownianMotion x) := by
      dsimp [A]
      fun_prop
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hu
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hv
    have hs := (summable_nat_add_iff 1).2
      ((h1.mul_left (∫ b, A b ∂(planarBrownianMotion x))).add (h2.mul_left 2))
    apply hs.congr
    intro n
    dsimp [R]
    rw [integral_add (hAi.mul_const _) (integrable_const _), integral_mul_const]
    simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
    rfl
  · intro b
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hu
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hv
    exact (summable_nat_add_iff 1).2 ((h1.mul_left (A b)).add (h2.mul_left 2))
  · intro n b
    dsimp [R]
    exact add_nonneg (mul_nonneg (hA b) (Real.exp_pos _).le) (by positivity)
  · filter_upwards [hb] with b hb
    intro g hg hgm hgs μ hμ n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    simpa only [one_pow, one_mul, mul_one, R, A, u, v] using hb g hg 1 zero_le_one hgm hgs μ hμ _ hpos hhalf

/-- The spatial factor in a nonpositive insertion is measurable and bounded
by one on each inner ball. -/
theorem nonpositive_insertion_inner_weight_properties
    {γ α ε δ : ℝ} (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε)
    (hεhalf : ε ≤ 1/2) (hδ : δ ≤ 1/2) :
    let g : ℂ → ℝ := {z : ℂ | ‖z‖ < δ}.indicator
      (fun z => (max (ε/2) ‖z‖) ^ (-γ*α))
    Measurable g ∧ (∀ z, |g z| ≤ 1) ∧
      (∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2) := by
  have hq : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  have hc : Continuous (fun z : ℂ => (max (ε/2) ‖z‖) ^ (-γ*α)) :=
    (Real.continuous_rpow_const hq).comp (continuous_const.max continuous_norm)
  refine ⟨hc.measurable.indicator (measurableSet_lt measurable_norm measurable_const), ?_, ?_⟩
  · intro z
    by_cases hz : ‖z‖ < δ
    · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | ‖z‖ < δ} from hz)]
      rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_one (by positivity) (by apply max_le <;> linarith) hq
    · simp [Set.indicator_of_notMem (show z ∉ {z : ℂ | ‖z‖ < δ} from hz)]
  · intro z hz
    have hz' : ‖z‖ < δ := by
      by_contra h
      exact hz (by simp [Set.indicator_of_notMem (show z ∉ {z : ℂ | ‖z‖ < δ} from h)])
    linarith

/-- The weighted zero-insertion increment along a unit-time path. -/
noncomputable def weightedInnerZeroTimeIncrement {Ω : Type*}
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ : ℝ) (g : ℂ → ℝ) (n : ℕ)
    (q : ContinuousPath ℂ × Ω) : ℝ :=
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  ∫ s in (0 : ℝ)..1, g (q.1 s.toNNReal) *
    ((ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) (ε/2) (q.1 s.toNNReal)) -
     ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.2) ε (q.1 s.toNNReal)))

/-- Bounded measurable weights give field-integrable spatial increments. -/
theorem integrable_weighted_inner_increment_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (γ : ℝ) (b : ContinuousPath ℂ)
    (g : ℂ → ℝ) (hg : Measurable g) (hgm : ∀ z, |g z| ≤ 1)
    (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2) :
    Integrable (fun ω => ∫ z, g z *
      ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
       ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))
      ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))) P := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hgi : Integrable g μ := by
    apply (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
    filter_upwards with z
    simpa only [Real.norm_eq_abs] using hgm z
  exact hh.integrable_integral_increment hε zero_lt_one μ hg hgi
    (fun z hz => by linarith [hgs z hz]) γ

/-- Weighted increments admit jointly measurable versions that agree with their
actual time integrals on one field event. -/
theorem exists_measurable_weighted_inner_time_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (g : ℕ → ℂ → ℝ) (hg : ∀ n, Measurable (g n)) :
    ∃ F : ℕ → ContinuousPath ℂ × Ω → ℝ, (∀ n, Measurable (F n)) ∧
      (∀ᵐ ω ∂P, ∀ b n, F n (b, ω) = weightedInnerZeroTimeIncrement hcirc γ (g n) n (b, ω)) ∧
      ∀ᵐ ω ∂P, ∀ b n, F n (b, ω) = ∫ z, g n z *
        ((((2 : ℝ)⁻¹ ^ (n+1))/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (((2 : ℝ)⁻¹ ^ (n+1))/2) z-hcirc ω 1 0)) -
        ((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ*(hcirc ω ((2 : ℝ)⁻¹ ^ (n+1)) z-hcirc ω 1 0)))
        ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let G : ℕ → Ω × ℂ → ℝ := fun n q => g n q.2 *
    ((ε n/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε n/2) q.2-H q.1 1 0)) -
    (ε n)^(γ^2/2) * Real.exp (γ*(H q.1 (ε n) q.2-H q.1 1 0)))
  have hG (n : ℕ) : Measurable (G n) := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε n/2) q.2) :=
      (hHm (ε n/2) (half_pos (hε n))).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 (ε n) q.2) :=
      (hHm (ε n) (hε n)).comp measurable_swap
    have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    exact ((hg n).comp measurable_snd).mul
      ((measurable_const.mul (measurable_const.mul (h1.sub h3)).exp).sub
        (measurable_const.mul (measurable_const.mul (h2.sub h3)).exp))
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
  refine ⟨F, hF, ?_, ?_⟩
  · filter_upwards [hHae, ae_recentered_inserted_circle_average hh 0] with ω hω hrec b n
    rw [show F n (b, ω) = ∫ s in (0 : ℝ)..1, G n (ω, b s.toNNReal) from
      unit_path_occupation_integral_eq_time b (fun z => G n (ω,z))
        ((hG n).comp (measurable_const.prodMk measurable_id))]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [G, hω, ε]
    rw [← hrec _ _ (half_pos (hε n)), ← hrec _ _ (hε n)]
    simp [ε]
  · filter_upwards [hHae] with ω hω b n
    simp only [F, G, hω, ε, ν]

/-- The annealed absolute weighted increments are bounded by a summable
sequence, simultaneously for any deterministic sequence of bounded weights. -/
theorem exists_summable_annealed_weighted_inner_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) (g : ℕ → ℂ → ℝ)
    (hg : ∀ n, Measurable (g n)) (hgm : ∀ n z, |g n z| ≤ 1)
    (hgs : ∀ n z, g n z ≠ 0 → ‖z‖ ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      ∀ n, Integrable (weightedInnerZeroTimeIncrement hcirc γ (g n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |weightedInnerZeroTimeIncrement hcirc γ (g n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  have := hh.isProbabilityMeasure
  obtain ⟨R, hRi, hRs, _, hR0, hRbound⟩ :=
    exists_integrable_summable_weighted_inner_increment_envelope hh hγ0 hγ2 x
  obtain ⟨F, hFm, hFtime, hFspatial⟩ :=
    exists_measurable_weighted_inner_time_increments hh γ g hg
  refine ⟨fun n => ∫ b, R n b ∂(planarBrownianMotion x), hRs,
    fun n => integral_nonneg (hR0 n), ?_⟩
  intro n
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F n (b,ω)) P := by
    apply (integrable_weighted_inner_increment_field hh hpos hhalf γ b (g n)
      (hg n) (hgm n) (hgs n)).congr
    filter_upwards [hFspatial] with ω hω
    exact (hω b n).symm
  have hbound : ∀ᵐ b ∂(planarBrownianMotion x), (∫ ω, ‖F n (b,ω)‖ ∂P) ≤ R n b := by
    filter_upwards [hRbound] with b hb
    have heq : (∫ ω, ‖F n (b,ω)‖ ∂P) = ∫ ω, |∫ z, g n z *
        ((((2 : ℝ)⁻¹ ^ (n+1))/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (((2 : ℝ)⁻¹ ^ (n+1))/2) z-hcirc ω 1 0)) -
        ((2 : ℝ)⁻¹ ^ (n+1))^(γ^2/2) * Real.exp (γ*(hcirc ω ((2 : ℝ)⁻¹ ^ (n+1)) z-hcirc ω 1 0)))
        ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))| ∂P := by
      apply integral_congr_ae
      filter_upwards [hFspatial] with ω hω
      rw [hω b n, Real.norm_eq_abs]
    rw [heq]
    exact hb (g n) (hg n) (hgm n) (hgs n) _ le_rfl n
  have hsec : Integrable (fun b => ∫ ω, ‖F n (b,ω)‖ ∂P) (planarBrownianMotion x) := by
    apply (hRi n).mono' ((hFm n).stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards [hbound] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb
  have hFi : Integrable (F n) ((planarBrownianMotion x).prod P) :=
    (integrable_prod_iff (hFm n).aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hfield, hsec⟩
  have hprod : ∀ᵐ q ∂((planarBrownianMotion x).prod P),
      F n q = weightedInnerZeroTimeIncrement hcirc γ (g n) n q := by
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

/-- The actual insertion-weighted zero-insertion increments have summable
annealed bounds for every deterministic cutoff sequence. -/
theorem exists_summable_annealed_nonpositive_weighted_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
      (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      ∀ n, Integrable (weightedInnerZeroTimeIncrement hcirc γ (g n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |weightedInnerZeroTimeIncrement hcirc γ (g n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
    (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
  have hp (n : ℕ) : Measurable (g n) ∧ (∀ z, |g n z| ≤ 1) ∧
      (∀ z, g n z ≠ 0 → ‖z‖ ≤ 1/2) := by
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    exact nonpositive_insertion_inner_weight_properties hγ0.le hα hpos hhalf (hδ n)
  exact exists_summable_annealed_weighted_inner_increments hh hγ0 hγ2 x g
    (fun n => (hp n).1) (fun n => (hp n).2.1) (fun n => (hp n).2.2)

/-- The actual insertion-weighted increments are almost surely summable and
their annealed expected tails tend to zero. -/
theorem exists_vanishing_annealed_nonpositive_weighted_tail
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
      (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      Filter.Tendsto (fun N => ∑' k, A (k+N)) Filter.atTop (nhds 0) ∧
      (∀ᵐ q ∂((planarBrownianMotion x).prod P),
        Summable (fun n => |weightedInnerZeroTimeIncrement hcirc γ (g n) n q|)) ∧
      ∀ N, (∫ q, ∑' k, |weightedInnerZeroTimeIncrement hcirc γ (g (k+N)) (k+N) q|
        ∂((planarBrownianMotion x).prod P)) ≤ ∑' k, A (k+N) := by
  let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
    (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
  obtain ⟨A, hA, hA0, hinc⟩ :=
    exists_summable_annealed_nonpositive_weighted_increments hh hγ0 hγ2 hα x δ hδ
  let μ := (planarBrownianMotion x).prod P
  let f : ℕ → ContinuousPath ℂ × Ω → ℝ := fun n q =>
    |weightedInnerZeroTimeIncrement hcirc γ (g n) n q|
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
