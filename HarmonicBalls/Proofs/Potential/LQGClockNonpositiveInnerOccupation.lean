import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInnerSupremum
import HarmonicBalls.Proofs.Potential.LQGClockInnerOccupationTransfer

/-! # Integrable bounds for inner clock increments

Brownian Riesz energy provides an integrable geometric envelope for inner increments.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A geometric envelope for all inner-ball field increments is integrable in
Brownian motion at each scale and summable for every path. -/
theorem exists_integrable_summable_inner_increment_envelope
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
      ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ : ℝ, δ ≤ 1/2 → ∀ μ : Measure ℂ,
      μ ≤ Measure.map (fun t => b t) ν → ∀ n : ℕ,
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        (∫ ω, |∫ z, ({z : ℂ | ‖z‖ < δ}.indicator (fun _ => (1 : ℝ)) z) *
          ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤ R n b := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hb⟩ :=
    ae_brownian_inner_ball_increment_le_riesz_energy hh hγ0 hγ2 x
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
    intro δ hδ μ hμ n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    exact hb δ hδ μ hμ _ hpos hhalf

/-- An inner increment is field-integrable for each continuous path. -/
theorem integrable_inner_increment_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hδ : δ ≤ 1/2)
    (γ : ℝ) (b : ContinuousPath ℂ) :
    Integrable (fun ω => ∫ z,
      ({z : ℂ | ‖z‖ < δ}.indicator (fun _ => (1 : ℝ)) z) *
      ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
       ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))
      ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))))) P := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  let g : ℂ → ℝ := {z : ℂ | ‖z‖ < δ}.indicator (fun _ => 1)
  have hgm : Measurable g := measurable_const.indicator (measurableSet_lt measurable_norm measurable_const)
  have hgi : Integrable g μ := by
    exact (inner_indicator_integrable_and_lintegral_eq b (fun _ => (1 : ℝ))
      continuous_const (fun _ => zero_le_one) hδ).1
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1 := by
    intro z hz
    have hz' : ‖z‖ < δ := by
      by_contra h
      exact hz (by simp [g, h])
    linarith
  exact hh.integrable_integral_increment hε zero_lt_one μ hgm hgi hgs γ

/-- For almost every path, each sequence of inner radii admits a full-field
 event on which the corresponding dyadic spatial increments are summable. -/
theorem planarBrownianMotion_ae_field_ae_summable_inner_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ : ℕ → ℝ, (∀ n, δ n ≤ 1/2) →
      ∀ᵐ ω ∂P, Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ z, ({z : ℂ | ‖z‖ < δ n}.indicator (fun _ => (1 : ℝ)) z) *
          ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))
          ∂(Measure.map (fun t => b t) ν)|) := by
  filter_upwards [planarBrownianMotion_ae_summable_inner_increment hh hγ0 hγ2 x] with b hb
  intro δ hδ
  apply LatticeProb.Gauss.ae_summable_of_summable_integral _ (fun _ _ => abs_nonneg _) _
  · intro n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    exact (integrable_inner_increment_field hh hpos hhalf (hδ n) γ b).abs
  · exact hb δ hδ (fun _ => Measure.map (fun t => b t) _) (fun _ => le_rfl)

/-- A measurable spatial function integrated against unit-time path occupation
is its real time integral along the path. -/
theorem unit_path_occupation_integral_eq_time
    (b : ContinuousPath ℂ) (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))))) =
      ∫ s in (0 : ℝ)..1, f (b s.toNNReal) := by
  rw [integral_map b.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  rw [integral_map (f := fun t : ℝ≥0 => f (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hf.comp b.continuous.measurable).aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]

/-- On one field event, every positive-scale inner increment has the same
spatial and real-time integral for every continuous path and radius. -/
theorem ae_inner_zero_increment_occupation_eq_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (ε δ : ℝ), 0 < ε → ∀ b : ContinuousPath ℂ,
      (∫ z, ({z : ℂ | ‖z‖ < δ}.indicator (fun _ => (1 : ℝ)) z) *
        ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
         ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0)))
        ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))) =
      ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))
          (b s.toNNReal) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh 0] with ω hω hrec
  intro ε δ hε b
  let f : ℂ → ℝ := fun z => ({z : ℂ | ‖z‖ < δ}.indicator (fun _ => (1 : ℝ)) z) *
    ((ε/2)^(γ^2/2) * Real.exp (γ*(H ω (ε/2) z-H ω 1 0)) -
     ε^(γ^2/2) * Real.exp (γ*(H ω ε z-H ω 1 0)))
  have hf : Measurable f := by
    dsimp [f]
    exact (measurable_const.indicator (measurableSet_lt measurable_norm measurable_const)).mul
      ((measurable_const.mul (measurable_const.mul ((hHc ω (ε/2) (half_pos hε)).measurable.sub measurable_const)).exp).sub
      (measurable_const.mul (measurable_const.mul ((hHc ω ε hε).measurable.sub measurable_const)).exp))
  have heq (z : ℂ) : f z = {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) z := by
    simp only [f, hω, Set.indicator_apply]
    split_ifs
    · simp only [one_mul, ← hrec (ε/2) z (half_pos hε), ← hrec ε z hε, zero_mul, sub_zero]
    · simp
  calc
    _ = ∫ z, f z ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1)))) := by simp only [f, hω]
    _ = ∫ s in (0 : ℝ)..1, f (b s.toNNReal) := unit_path_occupation_integral_eq_time b f hf
    _ = _ := by simp only [heq]

/-- For almost every Brownian path and every sequence of inner radii at most
one half, the actual zero-insertion time increments are summable for almost
 every field. -/
theorem planarBrownianMotion_ae_field_ae_summable_inner_zero_time_increment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ : ℕ → ℝ, (∀ n, δ n ≤ 1/2) →
      ∀ᵐ ω ∂P, Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ n}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))
            (b s.toNNReal)|) := by
  filter_upwards [planarBrownianMotion_ae_field_ae_summable_inner_increment hh hγ0 hγ2 x] with b hb
  intro δ hδ
  filter_upwards [hb δ hδ, ae_inner_zero_increment_occupation_eq_time hh γ] with ω hs heq
  apply hs.congr
  intro n
  exact congrArg abs (heq ((2 : ℝ)⁻¹ ^ (n+1)) (δ n) (by positivity) b)

end HarmonicBalls
