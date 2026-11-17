import HarmonicBalls.Proofs.Potential.LQGClockBrownianRadiusIncrement
import LatticeProb.LQG.GMCDyadicLimit
import LatticeProb.Gauss.RegressionDualCauchy

/-! # Dyadic Brownian occupation increments

Field increments against bounded Brownian occupation submeasures are summable
along dyadic scales.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For each fixed sequence of Brownian occupation submeasures, the absolute
weighted dyadic field increments are almost surely summable. -/
theorem ae_brownian_field_summable_submeasure_increments_of_radius
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ R - 1 / 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ μ : ℕ → Measure ℂ,
      (∀ n, μ n ≤ Measure.map (fun t => b t) ν) → ∀ᵐ ω ∂P,
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω R 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω R 0))) ∂(μ n)|) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hb⟩ :=
    ae_brownian_submeasure_field_increment_le_of_radius hh hγ0 hγ2 x hR hg hM hgM hgs
  filter_upwards [hb] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  intro μ hμ
  let c : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  let K : ℝ := ((Real.exp (γ^2*Real.log 2)-1)*
    Real.exp (Real.log R * (2*γ^2-(2*γ-θ)^2/2))*C+1)/2
  let L : ℝ := 2*M*Real.exp (Real.log R * (γ^2/2-(θ-γ)^2/2))
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hs : Summable (fun n : ℕ => K * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * c) +
      L * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1)) * e)) := by
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hc
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul he
    exact (summable_nat_add_iff 1).2 ((h1.mul_left K).add (h2.mul_left L))
  have hsum : Summable (fun n : ℕ =>
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      ∫ ω, |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω R 0)) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω R 0))) ∂(μ n)| ∂P) := by
    apply Summable.of_nonneg_of_le (fun n => integral_nonneg (fun ω => abs_nonneg _)) _ hs
    intro n
    have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
    have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    exact hb (μ n) (hμ n) _ hpos hhalf
  apply LatticeProb.Gauss.ae_summable_of_summable_integral _ (fun _ _ => abs_nonneg _) hsum
  intro n
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  have hgρ : Integrable g ρ := by
    refine (integrable_const M).mono' hg.aestronglyMeasurable ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgM z
  let : IsFiniteMeasure (μ n) := isFiniteMeasure_of_le ρ (hμ n)
  have hgi : Integrable g (μ n) := hgρ.mono_measure (hμ n)
  exact (hh.integrable_integral_increment hpos hR (μ n) hg hgi
    (fun z hz => by linarith [hgs z hz]) γ).abs

/-- The same summability holds after changing to the unit-circle normalization. -/
theorem ae_brownian_field_summable_submeasure_increments
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ R - 1 / 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ μ : ℕ → Measure ℂ,
      (∀ n, μ n ≤ Measure.map (fun t => b t) ν) → ∀ᵐ ω ∂P,
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂(μ n)|) := by
  filter_upwards [ae_brownian_field_summable_submeasure_increments_of_radius
    hh hγ0 hγ2 x hR hg hM hgM hgs] with b hb
  intro μ hμ
  filter_upwards [hb μ hμ] with ω hω
  let A : ℝ := Real.exp (γ * (hcirc ω R 0 - hcirc ω 1 0))
  have hA : 0 ≤ A := (Real.exp_pos _).le
  convert hω.mul_left A using 1
  funext n
  dsimp only
  rw [← abs_of_nonneg hA, ← abs_mul, ← integral_const_mul]
  congr 2
  funext z
  have he (r : ℝ) : Real.exp (γ * (hcirc ω r z - hcirc ω 1 0)) =
      A * Real.exp (γ * (hcirc ω r z - hcirc ω R 0)) := by
    dsimp [A]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he, he]
  ring

end HarmonicBalls
