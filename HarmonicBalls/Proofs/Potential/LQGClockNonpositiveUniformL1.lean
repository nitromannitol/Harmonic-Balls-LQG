import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveMeasurableLimit
import HarmonicBalls.Proofs.Potential.LQGClockNonpositiveInsertedAnnealedTail

/-! # Nonpositive half-disc clock integrability

Brownian occupation energy bounds for nonpositive inserted clocks.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric Filter
open scoped NNReal ENNReal Topology

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


/-- Zero-insertion clock occupation obeys one subcritical power bound
for every Brownian starting point. -/
theorem exists_uniform_lintegral_prod_brownian_inner_zero_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {ε δ : ℝ}, 0 < ε → ε ≤ 1/2 →
      0 < δ → δ ≤ 1/2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤ (ENNReal.ofReal δ) ^ (1/2 : ℝ) * C := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hball⟩ := planarBrownianMotion_unit_single_ball_occupation_le_uniform
    (d := (1/2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨ENNReal.ofReal C, ENNReal.ofReal_lt_top, ?_⟩
  intro x ε δ hε hεhalf hδ hδhalf
  have hbound :
      (∫⁻ b, ∫⁻ ω, ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z))) z
        ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1)))) ∂P ∂(planarBrownianMotion x)) ≤
        (ENNReal.ofReal δ) ^ (1/2 : ℝ) * ENNReal.ofReal C := by
    calc
      _ = ∫⁻ b, ∫⁻ t : ℝ≥0, (if ‖b t‖ < δ then 1 else 0 : ℝ≥0∞)
          ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
          ∂(planarBrownianMotion x) := by
        apply lintegral_congr
        intro b
        rw [lintegral_inner_inserted_density_eq hh hε hεhalf hδhalf γ 0]
        rw [lintegral_map (by
          apply Measurable.indicator
          · fun_prop
          · exact measurableSet_lt measurable_norm measurable_const) b.continuous.measurable]
        apply lintegral_congr
        intro t
        simp [Set.indicator_apply]
      _ ≤ ENNReal.ofReal (C * δ ^ (1/2 : ℝ)) := by
        simpa using hball x 0 δ hδ
      _ = _ := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_rpow_of_nonneg hδ.le]
        · exact mul_comm _ _
        · norm_num
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let A : Set ℂ := {z : ℂ | ‖z‖ < δ}
  let F : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun q =>
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage (0 : ℝ) (hcirc q.1) ε z)) (q.2 s.toNNReal))
  have hF : AEMeasurable F (P.prod (planarBrownianMotion x)) :=
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) hε γ (0 : ℝ) δ 0 1
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hA : MeasurableSet A := measurableSet_lt measurable_norm measurable_const
  have hmeas : ∀ᵐ ω ∂P, Measurable (fun z => ENNReal.ofReal
      (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage (0 : ℝ) (hcirc ω) ε w)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh (0 : ℝ)] with ω hω hrec
    have hm : Measurable (fun z : ℂ => ENNReal.ofReal
        (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          (H ω ε w - H ω 1 0 - (0 : ℝ) * Real.log (max ε ‖w‖)))) z)) := by
      apply ENNReal.measurable_ofReal.comp
      exact (measurable_const.mul (measurable_const.mul
        ((((hHm ε hε).comp (measurable_id.prodMk measurable_const)).sub measurable_const).sub
          (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp).indicator hA
    convert hm using 1
    ext z
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε z hε]
    · rfl
  have heq (b : ContinuousPath ℂ) : ∀ᵐ ω ∂P,
      F (ω,b) = ∫⁻ z, A.indicator (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage (0 : ℝ) (hcirc ω) ε z))) z ∂(ν.map b) := by
    filter_upwards [hmeas] with ω hω
    have heqfun : (fun z => ENNReal.ofReal (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage (0 : ℝ) (hcirc ω) ε w)) z)) =
        A.indicator (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage (0 : ℝ) (hcirc ω) ε z))) := by
      funext z
      simp only [Set.indicator_apply]
      split_ifs <;> simp
    rw [← heqfun, lintegral_map hω b.continuous.measurable]
    dsimp [F, ν]
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    symm
    exact lintegral_map (hω.comp b.continuous.measurable) continuous_real_toNNReal.measurable
  change (∫⁻ q, F q ∂(P.prod (planarBrownianMotion x))) ≤ _
  rw [lintegral_prod_symm _ hF]
  refine (le_of_eq ?_).trans hbound
  apply lintegral_congr
  intro b
  apply lintegral_congr_ae
  filter_upwards [heq b] with ω hω
  exact hω


/-- The smoothing correction has a single annealed power bound for all
Brownian starting points. -/
theorem exists_uniform_annealed_nonpositive_insertion_correction_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ α : ℝ) (hγ : 0 < γ) (hα : α ≤ 0) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧ ∀ (x : ℂ) {ε δ : ℝ},
      0 < ε → ε ≤ 1 / 2 → δ ≤ 1 / 2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1,
        ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          ((max ε ‖z‖) ^ (-γ * α) - (max (ε / 2) ‖z‖) ^ (-γ * α)) *
          (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z))) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤
      ENNReal.ofReal (ε ^ (-γ * α)) * ((ENNReal.ofReal ε) ^ (1 / 2 : ℝ) * C) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_lintegral_prod_brownian_inner_zero_le hh γ
  refine ⟨C + 1, by positivity, ENNReal.add_lt_top.mpr ⟨hC, by simp⟩, ?_⟩
  intro x ε δ hε hεhalf hδ
  calc
    _ ≤ ENNReal.ofReal (ε ^ (-γ * α)) *
        (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1,
          ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z)) (q.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro q
      dsimp only
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_mono
      intro s
      let z := q.2 s.toNNReal
      change ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator _ z) ≤
        ENNReal.ofReal (ε ^ (-γ * α)) * ENNReal.ofReal ({z : ℂ | ‖z‖ < ε}.indicator _ z)
      by_cases hzδ : ‖z‖ < δ
      · have hzhalf : ‖z‖ ≤ 1 / 2 := le_trans (le_of_lt hzδ) hδ
        have hstep := nonpositive_insertion_dyadic_density_increment
          (hcirc q.1) γ α ε z hγ.le hα hε hεhalf hzhalf
        dsimp only at hstep
        by_cases hzε : ‖z‖ < ε
        · rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < δ} from hzδ), Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < ε} from hzε),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hε.le _)]
          exact ENNReal.ofReal_le_ofReal hstep.2.2.2.2.2.2.2.2
        · have hzero := hstep.2.2.2.2.2.1 (le_of_not_gt hzε)
          rw [Set.indicator_of_mem (show z ∈ {w : ℂ | ‖w‖ < δ} from hzδ), Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < ε} from hzε), hzero, zero_mul,
            ENNReal.ofReal_zero, mul_zero]
      · rw [Set.indicator_of_notMem (show z ∉ {w : ℂ | ‖w‖ < δ} from hzδ), ENNReal.ofReal_zero]
        exact zero_le
    _ ≤ _ := by
      gcongr
      exact (hbound x hε hεhalf hε hεhalf).trans (by
        gcongr
        exact le_add_right le_rfl)


/-- Correction integrability and its geometric estimate hold with one
constant for every Brownian start. -/
theorem exists_uniform_integrable_nonpositive_insertion_corrections
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hα : α ≤ 0)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ C : ℝ≥0∞, 0 < C ∧ C < ∞ ∧ ∀ x : ℂ, ∀ n,
      Integrable (nonpositiveInsertionCorrection hcirc γ α (δ n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫⁻ q, ENNReal.ofReal (nonpositiveInsertionCorrection hcirc γ α (δ n) n q)
        ∂((planarBrownianMotion x).prod P)) ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ (n+1)) ^ (-γ*α)) *
          ((ENNReal.ofReal ((2 : ℝ)⁻¹ ^ (n+1))) ^ (1/2 : ℝ) * C) := by
  have := hh.isProbabilityMeasure
  obtain ⟨C, hC0, hC, hbound⟩ :=
    exists_uniform_annealed_nonpositive_insertion_correction_le hh γ α hγ0 hα
  refine ⟨C, hC0, hC, ?_⟩
  intro x
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
      _ ≤ _ := hbound x he hehalf (hδ n)
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


/-- The correction expectations have a summable bound independent of the
Brownian starting point. -/
theorem exists_uniform_summable_annealed_nonpositive_insertion_corrections
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hα : α ≤ 0)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ B : ℕ → ℝ, Summable B ∧ (∀ n, 0 ≤ B n) ∧ ∀ x : ℂ, ∀ n,
      Integrable (nonpositiveInsertionCorrection hcirc γ α (δ n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |nonpositiveInsertionCorrection hcirc γ α (δ n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ B n := by
  have := hh.isProbabilityMeasure
  obtain ⟨C, _, hC, hbound⟩ :=
    exists_uniform_integrable_nonpositive_insertion_corrections hh hγ0 hα δ hδ
  let B : ℕ → ℝ := fun n => C.toReal *
    Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * (1/2))
  have hB : Summable B := by
    exact (summable_nat_add_iff 1).2
      ((LatticeProb.Gauss.summable_exp_log_dyadicScale_mul (by norm_num : (0 : ℝ) < 1/2)).mul_left C.toReal)
  refine ⟨B, hB, fun n => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le, ?_⟩
  intro x n
  have hc := ae_nonpositive_insertion_correction_lintegral hh hγ0.le hα δ hδ
  let μ := (planarBrownianMotion x).prod P
  have hbound := hbound x
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


/-- Actual nonpositive inserted unit-time increments have summable
annealed bounds shared by all Brownian starting points. -/
theorem exists_uniform_summable_annealed_nonpositive_inserted_inner_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧ ∀ x : ℂ, ∀ n,
      Integrable (nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n)
        ((planarBrownianMotion x).prod P) ∧
      (∫ q, |nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q|
        ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  have := hh.isProbabilityMeasure
  let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
    (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
  obtain ⟨A, hA, hA0, hinc⟩ :=
    exists_uniform_summable_annealed_nonpositive_weighted_increments hh hγ0 hγ2 hα δ hδ
  obtain ⟨B, hB, hB0, hcorr⟩ :=
    exists_uniform_summable_annealed_nonpositive_insertion_corrections hh hγ0 hα δ hδ
  have heq := ae_nonpositive_inserted_inner_time_increment_eq hh hγ0.le hα δ hδ
  refine ⟨fun n => A n + B n, hA.add hB, fun n => add_nonneg (hA0 n) (hB0 n), ?_⟩
  intro x n
  let μ := (planarBrownianMotion x).prod P
  have heqprod : ∀ᵐ q ∂μ, ∀ n,
      nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q =
        weightedInnerZeroTimeIncrement hcirc γ (g n) n q -
          nonpositiveInsertionCorrection hcirc γ α (δ n) n q := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae heq] with q hq n
    exact hq q.1 n
  have hW := (hinc x n).1
  have hV := (hcorr x n).1
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
    _ ≤ _ := add_le_add (hinc x n).2 (hcorr x n).2


/-- A positive-time planar Brownian marginal is absolutely continuous
with respect to area measure. -/
theorem planarBrownianMotion_map_eval_absolutelyContinuous (x : ℂ) (t : ℝ≥0) (ht : t ≠ 0) :
    (planarBrownianMotion x).map (fun b => b t) ≪ volume := by
  have hmap := isFellerKernelSemigroup_planarHeatSemigroup.continuousProcess_map_eval_nnreal
    planarHeatSemigroup isConservative_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup t
  rw [← planarBrownianMotion_eq_continuousProcess] at hmap
  have hvalue := congrArg (fun ker : ProbabilityTheory.Kernel ℂ ℂ => ker x) hmap
  change (planarBrownianMotion.map (ContinuousPath.coordinateProcess t)) x = _ at hvalue
  rw [ProbabilityTheory.Kernel.map_apply _ (ContinuousPath.measurable_coordinateProcess t),
    planarHeatSemigroup_apply] at hvalue
  change (planarBrownianMotion x).map (ContinuousPath.coordinateProcess t) ≪ volume
  rw [hvalue]
  have h := (gaussianReal_absolutelyContinuous x.re ht).prod
    (gaussianReal_absolutelyContinuous x.im ht)
  have hm := h.map Complex.measurableEquivRealProd.symm.measurable
  rw [← Measure.volume_eq_prod ℝ ℝ, Complex.volume_preserving_equiv_real_prod.symm.map_eq] at hm
  exact hm

/-- Almost every Brownian path spends almost every positive time outside
a fixed area-null set. -/
theorem ae_planarBrownianMotion_ae_positive_time_avoids_null_set (x : ℂ)
    (S : Set ℂ) (hS : MeasurableSet S) (hnull : volume S = 0) :
    ∀ᵐ b ∂planarBrownianMotion x, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      b t.toNNReal ∉ S := by
  have hm : MeasurableSet {p : ContinuousPath ℂ × ℝ | p.1 p.2.toNNReal ∉ S} := by
    apply (hS.preimage ?_).compl
    fun_prop
  apply (Measure.ae_ae_comm hm).2
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : t.toNNReal ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr ht)
  have h := planarBrownianMotion_map_eval_absolutelyContinuous x t.toNNReal ht0 hnull
  change ((planarBrownianMotion x).map (ContinuousPath.coordinateProcess t.toNNReal)) S = 0 at h
  rw [Measure.map_apply (ContinuousPath.measurable_coordinateProcess t.toNNReal) hS] at h
  change (planarBrownianMotion x) {b | b t.toNNReal ∈ S} = 0 at h
  apply (ae_iff).2
  simpa only [not_not] using h

/-- Almost every Brownian path spends zero positive time on a fixed circle. -/
theorem ae_planarBrownianMotion_ae_positive_time_norm_ne (x : ℂ) (r : ℝ) :
    ∀ᵐ b ∂planarBrownianMotion x, ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ‖b t.toNNReal‖ ≠ r := by
  have h := ae_planarBrownianMotion_ae_positive_time_avoids_null_set x
    (sphere (0 : ℂ) r) isClosed_sphere.measurableSet (Measure.addHaar_sphere volume 0 r)
  simpa [Metric.mem_sphere, dist_zero_right] using h

/-- Closed and open half-disc occupation integrals agree for every
nonnegative horizon and spatial integrand, almost surely. -/
theorem ae_planarBrownianMotion_halfDisc_integral_eq_open (x : ℂ) :
    ∀ᵐ b ∂planarBrownianMotion x, ∀ (T : ℝ≥0) (f : ℂ → ℝ),
      (∫ s in (0 : ℝ)..(T : ℝ),
        {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) =
      ∫ s in (0 : ℝ)..(T : ℝ), {z : ℂ | ‖z‖ < 1/2}.indicator f (b s.toNNReal) := by
  filter_upwards [ae_planarBrownianMotion_ae_positive_time_norm_ne x (1/2)] with b hb T f
  rw [intervalIntegral.integral_of_le T.coe_nonneg, intervalIntegral.integral_of_le T.coe_nonneg]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Ioi_self hb] with s hs
  have h : ‖b s.toNNReal‖ ≤ (1/2 : ℝ) ↔ ‖b s.toNNReal‖ < 1/2 := by
    constructor
    · intro h
      exact lt_of_le_of_ne h hs
    · exact le_of_lt
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, norm_nonneg, true_and, h]

/-- A starting-point-uniform product-law bound survives every deterministic
Brownian time shift, with the independent field unchanged. -/
theorem lintegral_shift_prod_le_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (x : ℂ) (s : ℝ≥0)
    (F : ContinuousPath ℂ × Ω → ℝ≥0∞) (hF : Measurable F) (C : ℝ≥0∞)
    (hbound : ∀ y, (∫⁻ q, F q ∂((planarBrownianMotion y).prod P)) ≤ C) :
    (∫⁻ q, F (ContinuousPath.shift s q.1, q.2) ∂((planarBrownianMotion x).prod P)) ≤ C := by
  let K := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    planarHeatSemigroup isConservative_planarHeatSemigroup
  let : IsFiniteKernel (planarHeatSemigroup.kernel s) :=
    (planarHeatSemigroup.isSubMarkovKernel s).isFiniteKernel
  let ν := planarHeatSemigroup.kernel s x
  have hs : (planarBrownianMotion x).map (ContinuousPath.shift s) = K ∘ₘ ν := by
    rw [planarBrownianMotion_eq_continuousProcess]
    have hshift := congrArg (fun K => K x)
      (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup s)
    rw [Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s) x,
      Kernel.comp_apply] at hshift
    exact hshift
  have hG : Measurable (fun b => ∫⁻ ω, F (b,ω) ∂P) := hF.lintegral_prod_right'
  have hFs : Measurable (fun q : ContinuousPath ℂ × Ω => F (ContinuousPath.shift s q.1, q.2)) :=
    hF.comp (((ContinuousPath.measurable_shift_fixed s).comp measurable_fst).prodMk measurable_snd)
  calc
    _ = ∫⁻ b, ∫⁻ ω, F (ContinuousPath.shift s b,ω) ∂P ∂planarBrownianMotion x :=
      lintegral_prod _ hFs.aemeasurable
    _ = ∫⁻ b, ∫⁻ ω, F (b,ω) ∂P ∂((planarBrownianMotion x).map (ContinuousPath.shift s)) :=
      (lintegral_map hG (ContinuousPath.measurable_shift_fixed s)).symm
    _ = ∫⁻ y, ∫⁻ b, ∫⁻ ω, F (b,ω) ∂P ∂K y ∂ν := by
      rw [hs, Measure.lintegral_bind (Kernel.aemeasurable K) hG.aemeasurable]
    _ ≤ ∫⁻ _y, C ∂ν := by
      apply lintegral_mono
      intro y
      dsimp only [K]
      rw [← planarBrownianMotion_eq_continuousProcess]
      rw [← lintegral_prod _ hF.aemeasurable]
      exact hbound y
    _ = C := by simp [ν]

/-- The actual inserted inner increments admit jointly measurable versions,
simultaneously on one full-field event. -/
theorem exists_measurable_nonpositive_inserted_inner_time_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ F : ℕ → ContinuousPath ℂ × Ω → ℝ, (∀ n, Measurable (F n)) ∧
      ∀ᵐ ω ∂P, ∀ b n, F n (b,ω) =
        nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n (b,ω) := by
  let g : ℕ → ℂ → ℝ := fun n => {z : ℂ | ‖z‖ < δ n}.indicator
    (fun z => (max (((2 : ℝ)⁻¹ ^ (n+1))/2) ‖z‖) ^ (-γ*α))
  have hg (n : ℕ) : Measurable (g n) := by
    have hp : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hhf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    exact (nonpositive_insertion_inner_weight_properties hγ hα hp hhf (hδ n)).1
  obtain ⟨F, hFm, hFae, _⟩ := exists_measurable_weighted_inner_time_increments hh γ g hg
  obtain ⟨G, hGm, hGae⟩ := exists_measurable_nonpositive_insertion_corrections hh γ α δ
  have heq := ae_nonpositive_inserted_inner_time_increment_eq hh hγ hα δ hδ
  refine ⟨fun n q => F n q - G n q, fun n => (hFm n).sub (hGm n), ?_⟩
  filter_upwards [hFae, hGae, heq] with ω hF hG hI b n
  rw [hF b n, hG b n, hI b n]

/-- Actual inserted unit-block increments have one summable annealed bound
for all Brownian starts and deterministic time shifts. -/
theorem exists_uniform_summable_annealed_shifted_nonpositive_inserted_inner_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0)
    (δ : ℕ → ℝ) (hδ : ∀ n, δ n ≤ 1/2) :
    ∃ A : ℕ → ℝ, Summable A ∧ (∀ n, 0 ≤ A n) ∧ ∀ (x : ℂ) (s : ℝ≥0) n,
      Integrable (fun q => nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n
        (ContinuousPath.shift s q.1,q.2)) ((planarBrownianMotion x).prod P) ∧
      (∫ q, |nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n
        (ContinuousPath.shift s q.1,q.2)| ∂((planarBrownianMotion x).prod P)) ≤ A n := by
  have := hh.isProbabilityMeasure
  obtain ⟨A, hAs, hA0, hA⟩ :=
    exists_uniform_summable_annealed_nonpositive_inserted_inner_increments hh hγ0 hγ2 hα δ hδ
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_nonpositive_inserted_inner_time_increments hh hγ0.le hα δ hδ
  refine ⟨A, hAs, hA0, ?_⟩
  intro x s n
  let μ := (planarBrownianMotion x).prod P
  have hFs : Measurable (fun q : ContinuousPath ℂ × Ω => F n (ContinuousPath.shift s q.1,q.2)) :=
    (hFm n).comp (((ContinuousPath.measurable_shift_fixed s).comp measurable_fst).prodMk measurable_snd)
  have hprod (y : ℂ) : ∀ᵐ q ∂((planarBrownianMotion y).prod P),
      F n q = nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion y) (ν := P)).ae hFae] with q hq
    exact hq q.1 n
  have hbound (y : ℂ) : (∫⁻ q, ENNReal.ofReal |F n q|
      ∂((planarBrownianMotion y).prod P)) ≤ ENNReal.ofReal (A n) := by
    have hi : Integrable (fun q => F n q) ((planarBrownianMotion y).prod P) :=
      ((hA y n).1).congr ((hprod y).mono fun q hq => hq.symm)
    rw [← ofReal_integral_eq_lintegral_ofReal hi.abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _))]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ = ∫ q, |nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n q|
          ∂((planarBrownianMotion y).prod P) := by
        apply integral_congr_ae
        filter_upwards [hprod y] with q hq
        rw [hq]
      _ ≤ _ := (hA y n).2
  have hlin := lintegral_shift_prod_le_uniform P x s
    (fun q => ENNReal.ofReal |F n q|) ((hFm n).abs.ennreal_ofReal) (ENNReal.ofReal (A n)) hbound
  have hfin : (∫⁻ q, ENNReal.ofReal |F n (ContinuousPath.shift s q.1,q.2)| ∂μ) ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)
  have habs : Integrable (fun q => |F n (ContinuousPath.shift s q.1,q.2)|) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hFs.abs.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _))).1 hfin
  have hi : Integrable (fun q => F n (ContinuousPath.shift s q.1,q.2)) μ :=
    (integrable_norm_iff hFs.aestronglyMeasurable).1 (by simpa only [Real.norm_eq_abs] using habs)
  have heq : ∀ᵐ q ∂μ, F n (ContinuousPath.shift s q.1,q.2) =
      nonpositiveInsertedInnerTimeIncrement hcirc γ α (δ n) n (ContinuousPath.shift s q.1,q.2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hFae] with q hq
    exact hq (ContinuousPath.shift s q.1) n
  refine ⟨hi.congr heq, ?_⟩
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rw [← ofReal_integral_eq_lintegral_ofReal habs (Filter.Eventually.of_forall (fun _ => abs_nonneg _)),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => abs_nonneg _)), ENNReal.toReal_ofReal (hA0 n)] at hreal
  calc
    _ = ∫ q, |F n (ContinuousPath.shift s q.1,q.2)| ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with q hq
      rw [hq]
    _ ≤ _ := hreal

/-- The inserted open-disc clock accumulated during one unit of time. -/
noncomputable def innerInsertedUnitTimeClock {Ω : Type*}
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α ε δ : ℝ) (q : ContinuousPath ℂ × Ω) : ℝ :=
  ∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
    ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z))
      (q.1 s.toNNReal)

/-- The inserted unit clock has a nonnegative measurable version agreeing
on one full-field event for every path. -/
theorem exists_measurable_inner_inserted_unit_time_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) {ε : ℝ}
    (hε : 0 < ε) (δ : ℝ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧ (∀ q, 0 ≤ F q) ∧
      ∀ᵐ ω ∂P, ∀ b, F (b,ω) = innerInsertedUnitTimeClock hcirc γ α ε δ (b,ω) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let G : Ω × ℂ → ℝ := fun q => {z : ℂ | ‖z‖ < δ}.indicator
    (fun z => ε^(γ^2/2) * Real.exp (γ * (H q.1 ε z - H q.1 1 0 -
      α * Real.log (max ε ‖z‖)))) q.2
  have hG : Measurable G := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) := (hHm ε hε).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    apply Measurable.indicator _ ((measurableSet_lt measurable_norm measurable_const).preimage measurable_snd)
    exact measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let F : ContinuousPath ℂ × Ω → ℝ := fun q => ∫ z, G (q.2,z) ∂(Measure.map (fun t => q.1 t) ν)
  have hF : Measurable F := by
    have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
    have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
      heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have h := hG.comp ((measurable_snd.comp measurable_fst).prodMk heval)
    have hm := h.stronglyMeasurable.integral_prod_right' (ν := ν)
    convert hm.measurable using 1
    funext q
    exact integral_map q.1.continuous.measurable.aemeasurable
      (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine ⟨F, hF, ?_, ?_⟩
  · intro q
    apply integral_nonneg
    intro z
    dsimp [G]
    simp only [Set.indicator_apply]
    split_ifs <;> positivity
  · filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b
    rw [show F (b,ω) = ∫ s in (0 : ℝ)..1, G (ω,b s.toNNReal) from
      unit_path_occupation_integral_eq_time b (fun z => G (ω,z))
        (hG.comp (measurable_const.prodMk measurable_id))]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [G, hω, Set.indicator_apply]
    split_ifs
    · rw [← hrec ε _ hε]
    · rfl
/-- The real unit clock equals its nonnegative occupation integral on a
full-field event. -/
theorem ae_inner_inserted_unit_time_clock_lintegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : δ ≤ 1/2) :
    ∀ᵐ ω ∂P, ∀ b,
      0 ≤ innerInsertedUnitTimeClock hcirc γ α ε δ (b,ω) ∧
      ENNReal.ofReal (innerInsertedUnitTimeClock hcirc γ α ε δ (b,ω)) =
        ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε^(γ^2/2) * Real.exp
            (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b
  let f : ℂ → ℝ := fun z => ε^(γ^2/2) * Real.exp
    (γ * (H ω ε z - H ω 1 0 - α * Real.log (max ε ‖z‖)))
  have hf : Continuous f := by
    dsimp [f]
    have hlog : Continuous (fun z : ℂ => Real.log (max ε ‖z‖)) :=
      (continuous_const.max continuous_norm).log (fun _ => ne_of_gt (lt_max_of_lt_left hε))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (((hHc ω ε hε).sub continuous_const).sub (continuous_const.mul hlog))))
  have hf0 (z : ℂ) : 0 ≤ f z := by dsimp [f]; positivity
  have heq (z : ℂ) : {z : ℂ | ‖z‖ < δ}.indicator f z =
      {z : ℂ | ‖z‖ < δ}.indicator (fun z => ε^(γ^2/2) * Real.exp
        (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z := by
    simp only [f, hω, Set.indicator_apply]
    split_ifs
    · rw [← hrec ε z hε]
    · rfl
  have hint := inner_indicator_integrable_and_lintegral_eq b f hf hf0 hδ
  have htime : innerInsertedUnitTimeClock hcirc γ α ε δ (b,ω) =
      ∫ z, {z : ℂ | ‖z‖ < δ}.indicator f z ∂(Measure.map (fun t => b t)
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
    by_cases hz : ‖z‖ < δ
    · simpa [hz] using hf0 z
    · simp [hz]
  · rw [htime, ← hint.2]
    apply lintegral_congr
    intro s
    rw [heq]

/-- Nonpositive base clocks are integrable with one bound for all Brownian
starts and deterministic shifts. -/
theorem exists_uniform_integrable_shifted_nonpositive_inner_base_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hα : α ≤ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℂ) (s : ℝ≥0),
      Integrable (fun q => innerInsertedUnitTimeClock hcirc γ α (1/2) (1/2)
        (ContinuousPath.shift s q.1,q.2)) ((planarBrownianMotion x).prod P) ∧
      (∫ q, innerInsertedUnitTimeClock hcirc γ α (1/2) (1/2)
        (ContinuousPath.shift s q.1,q.2) ∂((planarBrownianMotion x).prod P)) ≤ C := by
  have := hh.isProbabilityMeasure
  obtain ⟨K, hK, hzero⟩ := exists_uniform_lintegral_prod_brownian_inner_zero_le hh γ
  let L : ℝ≥0∞ := (ENNReal.ofReal (1/2 : ℝ)) ^ (1/2 : ℝ) * K
  have hL : L < ∞ := ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top) hK
  obtain ⟨F, hFm, hF0, hFae⟩ := exists_measurable_inner_inserted_unit_time_clock hh γ α
    (by norm_num : (0 : ℝ) < 1/2) (1/2)
  have hlae := ae_inner_inserted_unit_time_clock_lintegral hh γ α
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) ≤ 1/2)
  have hw : ENNReal.ofReal ((1/2 : ℝ)^(-γ*α)) ≤ 1 := by
    have hp : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ.le) hα
    have h := Real.rpow_le_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num) hp
    simpa using ENNReal.ofReal_le_ofReal h
  have hbound (x : ℂ) : (∫⁻ q, ENNReal.ofReal (F q) ∂((planarBrownianMotion x).prod P)) ≤ L := by
    have heq : ∀ᵐ q ∂((planarBrownianMotion x).prod P), ENNReal.ofReal (F q) =
        ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < 1/2}.indicator (fun z => (1/2 : ℝ)^(γ^2/2) * Real.exp
            (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (1/2) z)) (q.1 t.toNNReal)) := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hFae,
        (Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hlae] with q hF hq
      rw [hF q.1, (hq q.1).2]
    calc
      _ = ∫⁻ q : ContinuousPath ℂ × Ω, (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < 1/2}.indicator (fun z => (1/2 : ℝ)^(γ^2/2) * Real.exp
            (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (1/2) z)) (q.1 t.toNNReal)))
          ∂((planarBrownianMotion x).prod P) := lintegral_congr_ae heq
      _ = ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < 1/2}.indicator (fun z => (1/2 : ℝ)^(γ^2/2) * Real.exp
            (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (1/2) z)) (q.2 t.toNNReal)))
          ∂(P.prod (planarBrownianMotion x)) := (lintegral_prod_swap _).symm
      _ ≤ ∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < 1/2}.indicator (fun z => (1/2 : ℝ)^(γ^2/2) * Real.exp
            (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (1/2) z)) (q.2 t.toNNReal)))
          ∂(P.prod (planarBrownianMotion x)) := by
        apply lintegral_mono
        intro q
        have h := inner_nonpositive_inserted_clock_le_zero (hcirc q.1) γ α (1/2) (1/2) 0 1 q.2
          hγ.le hα (by norm_num) le_rfl
        exact h.trans (by
          calc
            _ ≤ 1 * (∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal
              ({z : ℂ | ‖z‖ < 1/2}.indicator (fun z => (1/2 : ℝ)^(γ^2/2) * Real.exp
                (γ * LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) (1/2) z)) (q.2 t.toNNReal))) :=
                mul_le_mul_left hw _
            _ = _ := one_mul _)
      _ ≤ L := hzero x (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨L.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro x s
  let μ := (planarBrownianMotion x).prod P
  have hFs : Measurable (fun q : ContinuousPath ℂ × Ω => F (ContinuousPath.shift s q.1,q.2)) :=
    hFm.comp (((ContinuousPath.measurable_shift_fixed s).comp measurable_fst).prodMk measurable_snd)
  have hlin := lintegral_shift_prod_le_uniform P x s (fun q => ENNReal.ofReal (F q))
    hFm.ennreal_ofReal L hbound
  have hi : Integrable (fun q => F (ContinuousPath.shift s q.1,q.2)) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hFs.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun q => hF0 _))).1 (ne_of_lt (lt_of_le_of_lt hlin hL))
  have heq : ∀ᵐ q ∂μ, F (ContinuousPath.shift s q.1,q.2) =
      innerInsertedUnitTimeClock hcirc γ α (1/2) (1/2) (ContinuousPath.shift s q.1,q.2) := by
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hFae] with q hq
    exact hq (ContinuousPath.shift s q.1)
  refine ⟨hi.congr heq, ?_⟩
  have hreal := ENNReal.toReal_mono hL.ne hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun q => hF0 _)),
    ENNReal.toReal_ofReal (integral_nonneg (fun _ => hF0 _))] at hreal
  calc
    _ = ∫ q, F (ContinuousPath.shift s q.1,q.2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [heq] with q hq
      exact hq.symm
    _ ≤ _ := hreal


/-- Summable integral bounds yield an integrable envelope for every partial
sum of absolute values. -/
theorem exists_integrable_bound_of_summable_integral_abs
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : ℕ → X → ℝ)
    (hfi : ∀ n, Integrable (f n) μ) (A : ℕ → ℝ) (hA : Summable A)
    (hbound : ∀ n, (∫ x, |f n x| ∂μ) ≤ A n) :
    ∃ G : X → ℝ, Integrable G μ ∧ ∀ᵐ x ∂μ, ∀ N : ℕ,
      (∑ n ∈ Finset.range N, |f n x|) ≤ G x := by
  let S : X → ℝ≥0∞ := fun x => ∑' n, ENNReal.ofReal |f n x|
  have hm (n : ℕ) : AEMeasurable (fun x => ENNReal.ofReal |f n x|) μ :=
    (hfi n).abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hSm : AEMeasurable S μ := AEMeasurable.tsum hm
  have hfin : (∫⁻ x, S x ∂μ) < ∞ := by
    rw [show (fun x => S x) = (fun x => ∑' n, ENNReal.ofReal |f n x|) from rfl,
      lintegral_tsum hm]
    refine (ENNReal.tsum_le_tsum ?_).trans_lt hA.tsum_ofReal_lt_top
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hfi n).abs
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hbound n)
  refine ⟨fun x => (S x).toReal, integrable_toReal_of_lintegral_ne_top hSm hfin.ne, ?_⟩
  filter_upwards [ae_lt_top' hSm hfin.ne] with x hx N
  have hp : ENNReal.ofReal (∑ n ∈ Finset.range N, |f n x|) ≤ S x := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun n hn => abs_nonneg _)]
    exact ENNReal.sum_le_tsum _
  have h := ENNReal.toReal_mono hx.ne hp
  rw [ENNReal.toReal_ofReal (Finset.sum_nonneg fun n hn => abs_nonneg _)] at h
  exact h

private theorem intervalIntegrable_inner_clock_indicator (b : ContinuousPath ℂ)
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

/-- Each inserted dyadic increment equals the difference of consecutive
unit clocks on one full-field event. -/
theorem ae_inner_inserted_increment_eq_clock_sub
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ b n,
      nonpositiveInsertedInnerTimeIncrement hcirc γ α δ n (b,ω) =
        innerInsertedUnitTimeClock hcirc γ α (dyadicScale (n+2)) δ (b,ω) -
        innerInsertedUnitTimeClock hcirc γ α (dyadicScale (n+1)) δ (b,ω) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b n
  let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
  have he : 0 < ε := by dsimp [ε]; positivity
  let f : ℝ → ℂ → ℝ := fun r z => r^(γ^2/2) * Real.exp
    (γ * (H ω r z - H ω 1 0 - α * Real.log (max r ‖z‖)))
  have hf (r : ℝ) (hr : 0 < r) : Continuous (f r) := by
    dsimp [f]
    have hlog : Continuous (fun z : ℂ => Real.log (max r ‖z‖)) :=
      (continuous_const.max continuous_norm).log (fun _ => ne_of_gt (lt_max_of_lt_left hr))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (((hHc ω r hr).sub continuous_const).sub (continuous_const.mul hlog))))
  have heq (r : ℝ) (hr : 0 < r) (z : ℂ) : f r z =
      r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
    dsimp [f]
    rw [hω, hω, ← hrec r z hr]
  have hi1 := intervalIntegrable_inner_clock_indicator b (f (ε/2)) (hf _ (half_pos he)) δ
  have hi2 := intervalIntegrable_inner_clock_indicator b (f ε) (hf _ he) δ
  have hscale1 : dyadicScale (n+1) = ε := rfl
  have hscale2 : dyadicScale (n+2) = ε/2 := by
    dsimp [dyadicScale, ε]
    rw [show n+2 = (n+1)+1 by omega, pow_succ]
    ring
  rw [hscale1, hscale2]
  change (∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (fun z =>
      (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal)) = _
  calc
    _ = ∫ s in (0 : ℝ)..1, ({z : ℂ | ‖z‖ < δ}.indicator (f (ε/2)) (b s.toNNReal) -
        {z : ℂ | ‖z‖ < δ}.indicator (f ε) (b s.toNNReal)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [Set.indicator_apply]
      split_ifs <;> simp [heq _ (half_pos he), heq _ he]
    _ = (∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (f (ε/2)) (b s.toNNReal)) -
        (∫ s in (0 : ℝ)..1, {z : ℂ | ‖z‖ < δ}.indicator (f ε) (b s.toNNReal)) :=
      intervalIntegral.integral_sub hi1 hi2
    _ = _ := by
      congr 1 <;> apply intervalIntegral.integral_congr <;> intro s hs
      · simp only [Set.indicator_apply]
        split_ifs <;> simp [heq _ (half_pos he)]
      · simp only [Set.indicator_apply]
        split_ifs <;> simp [heq _ he]

/-- All dyadic unit clocks along one deterministic Brownian shift have a
common integrable product-law bound. -/
theorem exists_integrable_bound_shifted_nonpositive_inner_unit_clocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ) (s : ℝ≥0) :
    ∃ G : ContinuousPath ℂ × Ω → ℝ, Integrable G ((planarBrownianMotion x).prod P) ∧
      ∀ᵐ q ∂((planarBrownianMotion x).prod P), ∀ j : ℕ,
        |innerInsertedUnitTimeClock hcirc γ α (dyadicScale (j+1)) (1/2)
          (ContinuousPath.shift s q.1,q.2)| ≤ G q := by
  have := hh.isProbabilityMeasure
  obtain ⟨A, hAs, _, hA⟩ :=
    exists_uniform_summable_annealed_shifted_nonpositive_inserted_inner_increments
      hh hγ hγ2 hα (fun _ => 1/2) (fun _ => le_rfl)
  obtain ⟨C, _, hbase⟩ := exists_uniform_integrable_shifted_nonpositive_inner_base_clock hh hγ hα
  let μ := (planarBrownianMotion x).prod P
  let D : ℕ → ContinuousPath ℂ × Ω → ℝ := fun n q =>
    nonpositiveInsertedInnerTimeIncrement hcirc γ α (1/2) n (ContinuousPath.shift s q.1,q.2)
  let B : ℕ → ContinuousPath ℂ × Ω → ℝ := fun n q =>
    innerInsertedUnitTimeClock hcirc γ α (dyadicScale (n+1)) (1/2) (ContinuousPath.shift s q.1,q.2)
  have hD (n : ℕ) : Integrable (D n) μ := (hA x s n).1
  have hDb (n : ℕ) : (∫ q, |D n q| ∂μ) ≤ A n := (hA x s n).2
  obtain ⟨R, hR, hRb⟩ := exists_integrable_bound_of_summable_integral_abs μ D hD A hAs hDb
  have hB0 : Integrable (B 0) μ := by
    simpa [B, dyadicScale] using (hbase x s).1
  refine ⟨fun q => |B 0 q| + R q, hB0.abs.add hR, ?_⟩
  have heq := ae_inner_inserted_increment_eq_clock_sub hh γ α (1/2)
  filter_upwards [hRb, (Measure.quasiMeasurePreserving_snd
    (μ := planarBrownianMotion x) (ν := P)).ae heq] with q hq hinc j
  have hD_eq (n : ℕ) : D n q = B (n+1) q - B n q := by
    exact hinc (ContinuousPath.shift s q.1) n
  have ht : (∑ n ∈ Finset.range j, D n q) = B j q - B 0 q := by
    simp_rw [hD_eq]
    exact Finset.sum_range_sub (fun n => B n q) j
  calc
    |B j q| = |B 0 q + ∑ n ∈ Finset.range j, D n q| := by rw [ht]; congr 1; ring
    _ ≤ |B 0 q| + |∑ n ∈ Finset.range j, D n q| := abs_add_le _ _
    _ ≤ |B 0 q| + ∑ n ∈ Finset.range j, |D n q| := add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ |B 0 q| + R q := add_le_add le_rfl (hq j)

private theorem intervalIntegrable_open_halfDisc (f : ℂ → ℝ) (hf : Continuous f)
    (b : ContinuousPath ℂ) (a c : ℝ) :
    IntervalIntegrable (fun t : ℝ => {z : ℂ | ‖z‖ < 1/2}.indicator f (b t.toNNReal)) volume a c := by
  classical
  let p : ℝ → ℂ := fun t => b t.toNNReal
  have hp : Continuous p := b.continuous.comp continuous_real_toNNReal
  have hA : MeasurableSet (p ⁻¹' {z : ℂ | ‖z‖ < 1/2}) :=
    (measurableSet_lt measurable_norm measurable_const).preimage hp.measurable
  have hi := (hf.comp hp).intervalIntegrable (μ := volume) a c
  rw [intervalIntegrable_iff] at hi ⊢
  convert hi.indicator hA using 1
  funext t
  rw [Set.indicator_apply, Set.indicator_apply]
  rfl

/-- An integer-horizon open-disc occupation is the sum of its shifted
unit-block occupations. -/
theorem open_halfDisc_clock_sum_shifted_blocks (f : ℂ → ℝ) (hf : Continuous f)
    (b : ContinuousPath ℂ) (N : ℕ) :
    (∫ t in (0 : ℝ)..(N : ℝ), {z : ℂ | ‖z‖ < 1/2}.indicator f (b t.toNNReal)) =
    ∑ k ∈ Finset.range N, ∫ t in (0 : ℝ)..1,
      {z : ℂ | ‖z‖ < 1/2}.indicator f ((ContinuousPath.shift k b) t.toNNReal) := by
  let g : ℝ → ℝ := fun t => {z : ℂ | ‖z‖ < 1/2}.indicator f (b t.toNNReal)
  have hi (k : ℕ) : IntervalIntegrable g volume (k : ℝ) (k+1 : ℕ) :=
    intervalIntegrable_open_halfDisc f hf b k (k+1 : ℕ)
  have hs := intervalIntegral.sum_integral_adjacent_intervals (n := N) (fun k hk => hi k)
  have heq (k : ℕ) : (∫ t in (0 : ℝ)..1,
      {z : ℂ | ‖z‖ < 1/2}.indicator f ((ContinuousPath.shift k b) t.toNNReal)) =
      ∫ t in (k : ℝ)..((k : ℝ)+1), g t := by
    have hshift : (∫ t in (0 : ℝ)..1,
        {z : ℂ | ‖z‖ < 1/2}.indicator f ((ContinuousPath.shift k b) t.toNNReal)) =
        ∫ t in (0 : ℝ)..1, g ((k : ℝ) + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      dsimp only [g]
      simp only [ContinuousPath.shift_apply, Real.toNNReal_add (Nat.cast_nonneg k) ht.1,
        Real.toNNReal_natCast]
    rw [hshift, intervalIntegral.integral_comp_add_left]
    simp
  simp only [heq]
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, g] using hs.symm

/-- At every finite horizon the actual nonpositive dyadic half-disc clocks
have one integrable product-law bound, uniform in scale and time. -/
theorem exists_integrable_bound_nonpositive_halfDisc_clocks
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α ≤ 0) (x : ℂ) (T : ℝ≥0) :
    ∃ G : ContinuousPath ℂ × Ω → ℝ, Integrable G ((planarBrownianMotion x).prod P) ∧
      ∀ᵐ q ∂((planarBrownianMotion x).prod P), ∀ (j : ℕ) (t : ℝ≥0), t ≤ T →
        |∫ s in (0 : ℝ)..(t : ℝ),
          {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (dyadicScale (j+1)) z))
                (q.1 s.toNNReal)| ≤ G q := by
  have := hh.isProbabilityMeasure
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  let μ := (planarBrownianMotion x).prod P
  have hunit (k : ℕ) := exists_integrable_bound_shifted_nonpositive_inner_unit_clocks hh hγ hγ2 hα x k
  choose G hGi hGb using hunit
  let E : ContinuousPath ℂ × Ω → ℝ := fun q => ∑ k ∈ Finset.range N, G k q
  have hEi : Integrable E μ := by
    dsimp [E]
    exact integrable_finsetSum _ (fun k hk => hGi k)
  have hGbAll : ∀ᵐ q ∂μ, ∀ k j : ℕ,
      |innerInsertedUnitTimeClock hcirc γ α (dyadicScale (j+1)) (1/2)
        (ContinuousPath.shift k q.1,q.2)| ≤ G k q := by
    exact ae_all_iff.mpr (fun k => hGb k)
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ j : ℕ, Continuous (fun z =>
      (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec j
    have hc : Continuous (hcirc ω (dyadicScale (j+1))) := by
      rw [← funext (hω (dyadicScale (j+1)))]
      exact hHc ω (dyadicScale (j+1)) (dyadicScale_pos (j+1))
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z) =
        fun z => hcirc ω (dyadicScale (j+1)) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale (j+1)) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos (j+1))).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos (j+1))).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  refine ⟨E, hEi, ?_⟩
  filter_upwards [hGbAll,
    (Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hdensity,
    (Measure.quasiMeasurePreserving_fst (μ := planarBrownianMotion x) (ν := P)).ae
      (ae_planarBrownianMotion_halfDisc_integral_eq_open x)] with q hq hc hclose j t ht
  let f : ℂ → ℝ := fun z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (dyadicScale (j+1)) z)
  let g : ℝ → ℝ := fun s => {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (q.1 s.toNNReal)
  have hf0 (z : ℂ) : 0 ≤ f z := mul_nonneg (Real.rpow_nonneg (dyadicScale_pos (j+1)).le _)
    (Real.exp_pos _).le
  have hg0 (s : ℝ) : 0 ≤ g s := Set.indicator_nonneg (fun z _ => hf0 z) _
  have hnonneg : 0 ≤ ∫ s in (0 : ℝ)..(t : ℝ), g s :=
    intervalIntegral.integral_nonneg_of_forall t.coe_nonneg hg0
  have htN : (t : ℝ) ≤ N := le_trans (by exact_mod_cast ht) hN
  have hmono : (∫ s in (0 : ℝ)..(t : ℝ), g s) ≤ ∫ s in (0 : ℝ)..(N : ℝ), g s :=
    intervalIntegral.integral_mono_interval le_rfl t.coe_nonneg htN (Filter.Eventually.of_forall hg0)
      (intervalIntegrable_annular_density f (hc j) 0 q.1 0 N)
  have hsum : (∫ s in (0 : ℝ)..(N : ℝ), g s) =
      ∑ k ∈ Finset.range N, innerInsertedUnitTimeClock hcirc γ α (dyadicScale (j+1)) (1/2)
        (ContinuousPath.shift k q.1,q.2) := by
    have hcl : (∫ s in (0 : ℝ)..(N : ℝ), g s) =
        ∫ s in (0 : ℝ)..(N : ℝ), {z : ℂ | ‖z‖ < 1/2}.indicator f (q.1 s.toNNReal) := by
      simpa only [g, NNReal.coe_natCast] using hclose (N : ℝ≥0) f
    rw [hcl]
    simpa only [innerInsertedUnitTimeClock, f] using open_halfDisc_clock_sum_shifted_blocks f (hc j) q.1 N
  change |∫ s in (0 : ℝ)..(t : ℝ), g s| ≤ E q
  rw [abs_of_nonneg hnonneg]
  calc
    _ ≤ ∫ s in (0 : ℝ)..(N : ℝ), g s := hmono
    _ = _ := hsum
    _ ≤ ∑ k ∈ Finset.range N, G k q := by
      apply Finset.sum_le_sum
      intro k hk
      exact (le_abs_self _).trans (hq k j)
    _ = E q := rfl

/-- At each fixed Brownian start, the nonpositive inserted dyadic half-disc
clocks converge in uniform-time product-law L¹ on every finite horizon to the
same jointly measurable locally uniform limit. -/
theorem exists_measurable_uniform_L1_limit_nonpositive_halfDiscClock
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
      ∀ T : ℝ≥0, ∃ (A : ℕ → (Ω × ContinuousPath ℂ) → C(Icc (0 : ℝ) (T : ℝ), ℝ))
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
        Tendsto (fun j => ∫ p, ‖A j p - B p‖ ∂(P.prod (planarBrownianMotion x))) atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨F, hFm, hFc, hFlim⟩ :=
    exists_measurable_locally_uniform_limit_nonpositive_halfDiscClock hh x hγ hγ2 hα
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let R : Set ℂ := {z | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hR : MeasurableSet R := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let Z (j : ℕ) (ω : Ω) (z : ℂ) : ℝ := (dyadicScale (j+1))^(γ^2/2) *
    Real.exp (γ * (H ω (dyadicScale (j+1)) z - α * Real.log (max (dyadicScale (j+1)) ‖z‖)))
  have hZc (j : ℕ) (ω : Ω) : Continuous (Z j ω) := by
    dsimp [Z]
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hHc ω _ (dyadicScale_pos (j+1))).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos (j+1))).ne'))))))
  have hZm (j : ℕ) : Measurable (fun p : Ω × ℂ => Z j p.1 p.2) := by
    have he : Measurable (fun p : Ω × ℂ => H p.1 (dyadicScale (j+1)) p.2) :=
      (hHm _ (dyadicScale_pos (j+1))).comp measurable_swap
    exact measurable_const.mul (measurable_const.mul (he.sub (measurable_const.mul
      ((measurable_const.max measurable_snd.norm).log)))).exp
  let U (j : ℕ) (p : (Ω × ContinuousPath ℂ) × ℝ≥0) : ℝ :=
    ∫ s in (0 : ℝ)..(p.2 : ℝ), R.indicator (Z j p.1.1) (p.1.2 s.toNNReal)
  have hUm (j : ℕ) : Measurable (U j) := by
    have hev : Measurable (fun p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
        p.1.1.2 p.2.toNNReal) :=
      (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable.comp
        (measurable_fst.fst.snd.prodMk measurable_snd)
    have hI : Measurable (fun p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
        R.indicator (Z j p.1.1.1) (p.1.1.2 p.2.toNNReal)) := by
      convert (hZm j).comp (measurable_fst.fst.fst.prodMk hev) |>.indicator
        (hev hR) using 1
      ext p
      rfl
    have hS : MeasurableSet {p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ |
        0 < p.2 ∧ p.2 ≤ (p.1.2 : ℝ)} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp measurable_fst.snd))
    have h := (hI.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h.measurable using 1
    ext p
    dsimp only [U]
    rw [intervalIntegral.integral_of_le p.2.coe_nonneg, ← integral_indicator measurableSet_Ioc]
    rfl
  have hUc (j : ℕ) (p : Ω × ContinuousPath ℂ) : Continuous (fun t => U j (p,t)) := by
    exact (intervalIntegral.continuous_primitive
      (fun a c => intervalIntegrable_annular_density (Z j p.1) (hZc j p.1) 0 p.2 a c) 0).comp
        continuous_subtype_val
  have hUae : ∀ᵐ ω ∂P, ∀ j b t,
      U j ((ω,b),t) = ∫ s in (0 : ℝ)..(t : ℝ), R.indicator (fun z =>
        (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z))
            (b s.toNNReal) := by
    filter_upwards [hHae] with ω hω j b t
    apply intervalIntegral.integral_congr
    intro s hs
    apply congrArg (fun f : ℂ → ℝ => R.indicator f (b s.toNNReal))
    funext z
    have he : H ω (dyadicScale (j+1)) z = hcirc ω (dyadicScale (j+1)) z := hω _ _
    have hl : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z (dyadicScale (j+1)) =
        Real.log (max (dyadicScale (j+1)) ‖z‖) := by
      simpa using LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 (dyadicScale_pos (j+1))
    simp only [Z, LatticeProb.Gauss.fieldCircleAverage, hl, he]
  refine ⟨F, hFm, hFc, hFlim, ?_⟩
  intro T
  obtain ⟨G, hGi, hGb⟩ := exists_integrable_bound_nonpositive_halfDisc_clocks hh hγ hγlt hα x T
  let G' : Ω × ContinuousPath ℂ → ℝ := fun p => G (p.2,p.1)
  have hG'i : Integrable G' (P.prod (planarBrownianMotion x)) := hGi.swap
  let AT : ℕ → (Ω × ContinuousPath ℂ) → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun j p =>
    ⟨fun t => U j (p,(t : ℝ).toNNReal),
      (hUc j p).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  let BT : (Ω × ContinuousPath ℂ) → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun p =>
    ⟨fun t => F (p,(t : ℝ).toNNReal),
      (hFc p).1.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hATm (j : ℕ) : Measurable (AT j) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hUm j).comp (measurable_id.prodMk measurable_const)
  have hBTm : Measurable BT := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hFm.comp (measurable_id.prodMk measurable_const)
  have hUprod : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ j t,
      U j (p,t) = ∫ s in (0 : ℝ)..(t : ℝ), R.indicator (fun z =>
        (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
            (p.2 s.toNNReal) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hUae] with p hp
    intro j t
    exact hp j p.2 t
  have hswap : MeasurePreserving Prod.swap (P.prod (planarBrownianMotion x))
      ((planarBrownianMotion x).prod P) := Measure.measurePreserving_swap
  have hGb' := hswap.quasiMeasurePreserving.ae hGb
  have hATb : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ j, ‖AT j p‖ ≤ G' p := by
    filter_upwards [hGb', hUprod] with p hp he j
    have hG0 : 0 ≤ G' p := (abs_nonneg _).trans (hp 0 0 (zero_le : (0 : ℝ≥0) ≤ T))
    apply (ContinuousMap.norm_le (AT j p) hG0).2
    intro t
    have ht : (t : ℝ).toNNReal ≤ T := by
      exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
    have hb := hp j ((t : ℝ).toNNReal) ht
    change |U j (p,(t : ℝ).toNNReal)| ≤ G' p
    rw [he j ((t : ℝ).toNNReal)]
    simpa only [
      Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk, R, G', Prod.swap] using hb
  have hBT : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), Tendsto (fun j => AT j p) atTop (𝓝 (BT p)) := by
    filter_upwards [hFlim, hUprod] with p hp he
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hp T (ε/2) (half_pos hε)] with j hj
    have hle : ‖AT j p - BT p‖ ≤ ε/2 := by
      apply (ContinuousMap.norm_le (AT j p - BT p) (le_of_lt (half_pos hε))).2
      intro t
      have ht : (t : ℝ).toNNReal ≤ T := by
        exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
      have hx := (hj ((t : ℝ).toNNReal) ht).le
      change |U j (p,(t : ℝ).toNNReal) - F (p,(t : ℝ).toNNReal)| ≤ ε/2
      rw [he j ((t : ℝ).toNNReal)]
      simpa only [
        Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk, R] using hx
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hle (half_lt_self hε)
  obtain ⟨hi, ht⟩ := integral_uniform_distance_tendsto_of_dominated AT hATm BT G' hG'i hATb hBT
  refine ⟨AT, BT, hATm, hBTm, ?_, (fun _ _ => rfl), hi, ht⟩
  filter_upwards [hUprod] with p hp j t
  have he := hp j ((t : ℝ).toNNReal)
  simpa only [AT, ContinuousMap.coe_mk, Real.toNNReal_of_nonneg t.property.1,
    NNReal.coe_mk, R] using he

end HarmonicBalls
