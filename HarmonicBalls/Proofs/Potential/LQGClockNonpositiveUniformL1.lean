import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveMeasurableLimit
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInsertedAnnealedTail

/-! # Nonpositive half-disc clock integrability

Brownian occupation energy bounds for nonpositive inserted clocks.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The geometric occupation-energy envelope has a summable mean independent
of the Brownian starting point. -/
theorem exists_uniform_summable_inner_energy_bound {γ d u v : ℝ}
    (hd0 : 0 < d) (hd2 : d < 2) (hu : 0 < u) (hv : 0 < v) :
    ∃ A : ℕ → ℝ, Summable A ∧ ∀ x : ℂ, ∀ n : ℕ,
      Integrable (fun b => ((Real.exp (γ^2 * Real.log 2) - 1) *
        (unitOccupationRieszEnergy d b * 2^d) + 1) / 2 *
        Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
        2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v))
        (planarBrownianMotion x) ∧
      (∫ b, ((Real.exp (γ^2 * Real.log 2) - 1) *
        (unitOccupationRieszEnergy d b * 2^d) + 1) / 2 *
        Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
        2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
        ∂(planarBrownianMotion x)) = A n := by
  let B : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2 * Real.log 2) - 1) * (unitOccupationRieszEnergy d b * 2^d) + 1) / 2
  have hB (x : ℂ) : Integrable B (planarBrownianMotion x) := by
    have hE := integrable_unitOccupationRieszEnergy x hd0 hd2
    dsimp [B]
    fun_prop
  let c : ℝ := ∫ b, B b ∂(planarBrownianMotion 0)
  let A : ℕ → ℝ := fun n => c * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
    2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
  have hA : Summable A := by
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hu
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hv
    exact (summable_nat_add_iff 1).2 ((h1.mul_left c).add (h2.mul_left 2))
  refine ⟨A, hA, ?_⟩
  intro x n
  have hBc : (∫ b, B b ∂(planarBrownianMotion x)) = c := by
    dsimp [B, c]
    rw [integral_div, integral_div]
    congr 1
    rw [integral_add ((integrable_unitOccupationRieszEnergy x hd0 hd2).mul_const _ |>.const_mul _)
      (integrable_const _),
      integral_add ((integrable_unitOccupationRieszEnergy 0 hd0 hd2).mul_const _ |>.const_mul _)
      (integrable_const _)]
    simp only [integral_const_mul, integral_mul_const, integral_const, smul_eq_mul,
      Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
    rw [integral_unitOccupationRieszEnergy_eq x 0 hd0 hd2]
  refine ⟨?_, ?_⟩
  · change Integrable (fun b => B b * _ + _) _
    fun_prop
  · change (∫ b, B b * _ + _ ∂planarBrownianMotion x) = A n
    rw [integral_add ((hB x).mul_const _) (integrable_const _), integral_mul_const, hBc]
    simp [A]
private theorem exp_bound_algebra {u p d a q B C M I A : ℝ}
    (hB : 0 ≤ B)
    (hI : I ≤ C * Real.exp (u*d)) (hA : A ≤ M) :
    Real.exp (u*a) * ((B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) +
      Real.exp (u*((d-p)/2))) / 2 + 2*A*Real.exp (-u*q)) ≤
    (B*C+1)/2 * Real.exp (u*(a+(d-p)/2)) + 2*M*Real.exp (u*(a-q)) := by
  have h : B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) ≤
      B * Real.exp (-u*p) * (C * Real.exp (u*d)) / Real.exp (u*((d-p)/2)) := by
    gcongr
  have ha : 2*A*Real.exp (-u*q) ≤ 2*M*Real.exp (-u*q) := by gcongr
  calc
    _ ≤ Real.exp (u*a) * ((B * Real.exp (-u*p) * (C * Real.exp (u*d)) /
        Real.exp (u*((d-p)/2)) + Real.exp (u*((d-p)/2))) / 2 +
        2*M*Real.exp (-u*q)) := by gcongr
    _ = _ := by
      have h1 : Real.exp (u*a) * Real.exp (-u*p) * Real.exp (u*d) /
          Real.exp (u*((d-p)/2)) = Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      have h2 : Real.exp (u*a) * Real.exp (u*((d-p)/2)) =
          Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : Real.exp (u*a) * Real.exp (-u*q) = Real.exp (u*(a-q)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination (B*C/2)*h1 + (1/2)*h2 + (2*M)*h3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

private theorem field_increment_le_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε γ θ d C M : ℝ}
    (hε : 0 < ε) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1)
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2 * γ)
    (hA : (∫ z, |g z| ∂ν) ≤ M)
    (hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) ≤ C * Real.exp (Real.log ε * d)) :
    ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω (ε / 2) z - hcirc ω 1 0)) -
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0))) ∂ν| ∂P ≤
      ((Real.exp (γ ^ 2 * Real.log 2) - 1) * C + 1) / 2 *
        Real.exp (Real.log ε * ((d - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2)) +
      2 * M * Real.exp (Real.log ε * ((θ - γ) ^ 2 / 2)) := by
  let p : ℝ := 2 * γ ^ 2 - (2 * γ - θ) ^ 2 / 2
  let q : ℝ := γ ^ 2 / 2 - (θ - γ) ^ 2 / 2
  let u : ℝ := Real.log ε
  have hB : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hraw := hh.integral_abs_integral_increment_le hε (R := 1) zero_lt_one ν hgm hg hgR hγθ hθ
    (t := Real.exp (u * ((d - p) / 2))) (Real.exp_pos _)
  have hlog : Real.log (1 / ε) = -u := by simp [u]
  conv at hraw =>
    rhs
    rw [hlog, Real.rpow_def_of_pos hε]
  have halg := exp_bound_algebra (u := u) (p := p) (d := d) (a := γ ^ 2 / 2)
    (q := q) (B := Real.exp (γ ^ 2 * Real.log 2) - 1) hB hI hA
  refine hraw.trans ?_
  convert halg using 1; dsimp [p, q, u]; ring_nf


/-- One choice of exponents controls weighted inner increments for every
Brownian starting point, on a full event depending on that start. -/
theorem exists_uniform_exponents_brownian_weighted_increment_le_riesz_energy
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ x : ℂ, ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
        (∀ z, |g z| ≤ M) → (∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2) →
        ∀ μ : Measure ℂ, μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        (∫ ω, |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, _⟩ := exists_clock_truncation_exponents hγ0 hγ2
  refine ⟨θ, d, hγθ, hθ, hd0, hd2, hp, ?_⟩
  dsimp only
  intro x
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_occupation_le_riesz_energy x hd0 hd2] with b hb
  intro g hg M hM hgM hgs μ hμ ε hε hεhalf
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  have hgρ : Integrable g ρ := by
    refine (integrable_const M).mono' hg.aestronglyMeasurable ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgM z
  have hgi : Integrable g μ := hgρ.mono_measure hμ
  have hA : (∫ z, |g z| ∂μ) ≤ M := by
    calc
      _ ≤ ∫ z, |g z| ∂ρ := integral_mono_measure hμ (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hgρ.abs
      _ ≤ ∫ _ : ℂ, M ∂ρ := integral_mono hgρ.abs (integrable_const M) (fun z => hgM z)
      _ = M := by simp
  have hpair0 := hb g hg M hM hgM (2*ε) (by positivity)
  have hpair : (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < 2*ε then |g p.1| * |g p.2| else 0
      ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
    apply (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hpair0.1).trans hpair0.2.2
    filter_upwards with p
    split_ifs <;> positivity
  have hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (M^2*unitOccupationRieszEnergy d b*2^d)*Real.exp (Real.log ε*d) := by
    have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hpair
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hI'
    convert hI' using 1; ring
  exact field_increment_le_rate hh hε μ hg hgi (fun z hz => by linarith [hgs z hz])
    hγθ.le hθ.le hA hI


/-- Bounded inner weights have a summable annealed increment bound
that is independent of the Brownian starting point. -/
theorem exists_uniform_summable_annealed_weighted_inner_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (g : ℕ → ℂ → ℝ)
    (hg : ∀ n, Measurable (g n)) (hgm : ∀ n z, |g n z| ≤ 1)
    (hgs : ∀ n z, g n z ≠ 0 → ‖z‖ ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      ∀ x : ℂ, ∀ n, Integrable (weightedInnerZeroTimeIncrement hcirc γ (g n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |weightedInnerZeroTimeIncrement hcirc γ (g n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  have := hh.isProbabilityMeasure
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hbound⟩ :=
    exists_uniform_exponents_brownian_weighted_increment_le_riesz_energy hh hγ0 hγ2
  let u : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let v : ℝ := (θ-γ)^2/2
  have hu : 0 < u := by dsimp [u]; positivity
  have hv : 0 < v := by dsimp [v]; positivity
  let R : ℕ → ContinuousPath ℂ → ℝ := fun n b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(unitOccupationRieszEnergy d b * 2^d)+1)/2 *
      Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * u) +
      2 * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * v)
  obtain ⟨A, hAs, hA⟩ := exists_uniform_summable_inner_energy_bound
    (γ := γ) hd0 hd2 hu hv
  have hR0 (n : ℕ) (b : ContinuousPath ℂ) : 0 ≤ R n b := by
    dsimp [R]
    have he : 0 ≤ Real.exp (γ^2*Real.log 2)-1 :=
      sub_nonneg.mpr (Real.one_le_exp (by positivity))
    have hE : 0 ≤ unitOccupationRieszEnergy d b := ENNReal.toReal_nonneg
    positivity
  obtain ⟨F, hFm, hFtime, hFspatial⟩ :=
    exists_measurable_weighted_inner_time_increments hh γ g hg
  refine ⟨A, hAs, ?_, ?_⟩
  · intro n
    rw [← (hA 0 n).2]
    exact integral_nonneg (hR0 n)
  intro x n
  have hRi : Integrable (R n) (planarBrownianMotion x) := (hA x n).1
  have hRbound := hbound x
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
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have h := hb (g n) (hg n) 1 zero_le_one (hgm n) (hgs n) _ le_rfl _ hpos hhalf
    simpa only [one_pow, one_mul, mul_one, R, u, v] using h
  have hsec : Integrable (fun b => ∫ ω, ‖F n (b,ω)‖ ∂P) (planarBrownianMotion x) := by
    apply hRi.mono' ((hFm n).stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
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
    _ ≤ ∫ b, R n b ∂(planarBrownianMotion x) := integral_mono_ae hsec hRi hbound
    _ = A n := (hA x n).2


/-- Nonpositive insertion weights retain the same starting-point-uniform
summable annealed estimate. -/
theorem exists_uniform_summable_annealed_nonpositive_weighted_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
      (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧
      ∀ x : ℂ, ∀ n, Integrable (weightedInnerZeroTimeIncrement hcirc γ (g n) n)
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
  exact exists_uniform_summable_annealed_weighted_inner_increments hh hγ0 hγ2 g
    (fun n => (hp n).1) (fun n => (hp n).2.1) (fun n => (hp n).2.2)


/-- A single subcritical power bound controls expected unit-time ball
occupation for all Brownian starts and ball centers. -/
theorem planarBrownianMotion_unit_single_ball_occupation_le_uniform {d : ℝ}
    (hd0 : 0 < d) (hd2 : d < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x z : ℂ) (r : ℝ), 0 < r →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      (∫⁻ b, ∫⁻ t : ℝ≥0,
        (if ‖b t - z‖ < r then 1 else 0 : ℝ≥0∞) ∂ν
          ∂(planarBrownianMotion x)) ≤ ENNReal.ofReal (C * r ^ d) := by
  let q : ℝ := d / 2
  have hq0 : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hqd : 2 * q = d := by dsimp [q]; ring
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let K : ℝ≥0∞ := ∫⁻ t in Icc (0 : ℝ) 1, ‖t‖ₑ ^ (-q)
  have hK : K < ∞ := by
    have hsub : Icc (0 : ℝ) 1 ⊆ ball (0 : ℝ) 2 := by
      intro t ht
      simp only [mem_ball, Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [ht.1, ht.2]
    have hb : (∫⁻ t in ball (0 : ℝ) 2, ‖t‖ₑ ^ (-q)) < ∞ := by
      convert (show (∫⁻ t in ball (0 : ℝ) 2, ‖t - (0 : ℝ)‖ₑ ^ (-q)) < ∞ from ?_) using 1
      · simp
      rw [LatticeProb.PegdenSmart.lintegral_ball_enorm_sub_rpow volume 0 (by norm_num : (0 : ℝ) < 2)]
      apply ENNReal.mul_lt_top
      · apply ENNReal.rpow_lt_top_of_nonneg
        · simp only [Module.finrank_self, Nat.cast_one]; linarith
        · exact ENNReal.ofReal_ne_top
      · apply LatticeProb.PegdenSmart.lintegral_ball_enorm_rpow_lt_top volume
        simp only [Module.finrank_self, Nat.cast_one]; linarith
    exact (lintegral_mono_set hsub).trans_lt hb
  let C : ℝ := (2 / Real.pi) ^ q * (K.toReal + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x z r hr
  have hν : NullSingletonClass ν := by
    constructor
    intro t
    dsimp [ν]
    rw [Measure.map_apply continuous_real_toNNReal.measurable (measurableSet_singleton t),
      Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton t))]
    apply measure_mono_null _ (measure_singleton (t : ℝ))
    intro a ha
    have ht := congrArg (fun v : ℝ≥0 => (v : ℝ)) ha.1
    have ha0 : 0 ≤ a := ha.2.1
    simpa [Real.toNNReal_of_nonneg ha0] using ht
  let : NullSingletonClass ν := hν
  let E : Set (ContinuousPath ℂ × ℝ≥0) := {p | ‖p.1 p.2 - z‖ < r}
  have hE : MeasurableSet E := by
    apply isOpen_lt _ continuous_const |>.measurableSet
    fun_prop
  have hswap : (∫⁻ b, ∫⁻ t : ℝ≥0, (if ‖b t - z‖ < r then 1 else 0 : ℝ≥0∞) ∂ν
      ∂(planarBrownianMotion x)) = ∫⁻ t : ℝ≥0,
        planarBrownianMotion x {b | ‖b t - z‖ < r} ∂ν := by
    let F : ContinuousPath ℂ × ℝ≥0 → ℝ≥0∞ := E.indicator 1
    have hF : Measurable F := measurable_const.indicator hE
    calc
      _ = ∫⁻ b, ∫⁻ t, F (b,t) ∂ν ∂(planarBrownianMotion x) := by simp [F, E, Set.indicator_apply]
      _ = ∫⁻ t, ∫⁻ b, F (b,t) ∂(planarBrownianMotion x) ∂ν := lintegral_lintegral_swap hF.aemeasurable
      _ = _ := by
        congr 1; funext t
        have hm : MeasurableSet {b : ContinuousPath ℂ | ‖b t - z‖ < r} := by
          apply isOpen_lt _ continuous_const |>.measurableSet
          fun_prop
        convert lintegral_indicator_one hm using 1; simp [F, E, Set.indicator_apply]
  have hbound (t : ℝ≥0) (ht : t ≠ 0) :
      planarBrownianMotion x {b | ‖b t - z‖ < r} ≤
        ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d * |(t : ℝ)| ^ (-q)) := by
    have heq : planarBrownianMotion x {b | ‖b t - z‖ < r} =
        planarBrownianMotion x {b | ‖b t - b 0 - (z - x)‖ < r} := by
      apply measure_congr
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with b hb
      simp only [hb]
      congr 1
      congr 1
      abel
    rw [heq]
    simpa [hqd] using planarBrownianMotion_increment_smallBall_rpow_le_uniform_center x (z - x) ht hr hq0 hq1
  have hkernel : (∫⁻ t : ℝ≥0, ENNReal.ofReal (|(t : ℝ)| ^ (-q)) ∂ν) ≤ K := by
    rw [show ν = Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)) from rfl,
      lintegral_map (by fun_prop) continuous_real_toNNReal.measurable]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (volume.ae_ne (0 : ℝ))] with t ht ht0
    have hp : 0 < ‖t‖ := norm_pos_iff.mpr ht0
    simp only [Real.toNNReal_of_nonneg ht.1]
    change ENNReal.ofReal (‖t‖ ^ (-q)) ≤ ‖t‖ₑ ^ (-q)
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_pos hp]
  have hA : 0 ≤ (2 / Real.pi) ^ q * r ^ d := by positivity
  have hKbound : K ≤ ENNReal.ofReal (K.toReal + 1) := by
    calc
      K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hK.ne).symm
      _ ≤ ENNReal.ofReal (K.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  change (∫⁻ b, ∫⁻ t : ℝ≥0, (if ‖b t - z‖ < r then 1 else 0 : ℝ≥0∞) ∂ν
    ∂(planarBrownianMotion x)) ≤ ENNReal.ofReal (C * r ^ d)
  rw [hswap]
  calc
    _ ≤ ∫⁻ t : ℝ≥0, ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d * |(t : ℝ)| ^ (-q)) ∂ν := by
      apply lintegral_mono_ae
      filter_upwards [ν.ae_ne 0] with t ht
      exact hbound t ht
    _ = ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d) *
        (∫⁻ t : ℝ≥0, ENNReal.ofReal (|(t : ℝ)| ^ (-q)) ∂ν) := by
      simp_rw [ENNReal.ofReal_mul hA]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal ((2 / Real.pi) ^ q * r ^ d) * ENNReal.ofReal (K.toReal + 1) := by gcongr; exact hkernel.trans hKbound
    _ = ENNReal.ofReal (C * r ^ d) := by
      rw [← ENNReal.ofReal_mul hA]
      congr 1
      dsimp [C]
      ring


end HarmonicBalls
