import HarmonicBalls.Proofs.Potential.LQGClockBrownianRadiusSummability

/-! # Countable occupation tests

Weighted dyadic field occupations converge simultaneously for a countable
family of Brownian occupation submeasures.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped NNReal ENNReal
namespace HarmonicBalls

/-- For any specified countable family of unit-time Brownian occupation
submeasures, the weighted dyadic field occupations converge simultaneously. -/
theorem ae_brownian_field_tendsto_countable_occupation_tests
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) {R : ℝ} (hR : 0 < R)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ R - 1 / 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ μ : ι → Measure ℂ,
      (∀ i, μ i ≤ Measure.map (fun t => b t) ν) → ∀ᵐ ω ∂P,
      ∀ i, ∃ L : ℝ, Tendsto (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        ∫ z, g z * (ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂(μ i))
          atTop (𝓝 L) := by
  have hs := ae_brownian_field_summable_submeasure_increments hh hγ0 hγ2 x hR hg hM hgM hgs
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hs] with b hb
  intro μ hμ
  have hsum : ∀ᵐ ω ∂P, ∀ i, Summable (fun n : ℕ =>
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂(μ i)|) := by
    apply ae_all_iff.mpr
    intro i
    exact hb (fun _ => μ i) (fun _ => hμ i)
  filter_upwards [hsum, hcont] with ω hs hc i
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hstep (n : ℕ) : ε (n+1) = ε n / 2 := by
    dsimp [ε]
    rw [show n+1+1 = (n+1)+1 by omega, pow_succ]
    ring
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let ρ := Measure.map (fun t => b t) ν
  let D : ℕ → ℂ → ℝ := fun n z => (ε n)^(γ^2/2) *
    Real.exp (γ * (hcirc ω (ε n) z - hcirc ω 1 0))
  have hD (n : ℕ) : Continuous (D n) :=
    continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul ((hc _ (hε n)).sub continuous_const)))
  have hint (n : ℕ) : Integrable (fun z => g z * D n z) (μ i) := by
    have ht : Integrable (fun s : ℝ => D n (b s.toNNReal))
        (volume.restrict (Icc (0 : ℝ) 1)) :=
      ((hD n).comp (b.continuous.comp continuous_real_toNNReal)).integrableOn_Icc
    have hν : Integrable (fun t : ℝ≥0 => D n (b t)) ν :=
      (integrable_map_measure ((hD n).comp b.continuous).aestronglyMeasurable
        continuous_real_toNNReal.measurable.aemeasurable).2 ht
    have hρ : Integrable (D n) ρ :=
      (integrable_map_measure (hD n).aestronglyMeasurable b.continuous.measurable.aemeasurable).2 hν
    exact ((hρ.mono_measure (hμ i)).bdd_mul hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hgM z))
  let A : ℕ → ℝ := fun n => ∫ z, g z * D n z ∂(μ i)
  have hdist : Summable (fun n => dist (A n) (A (n+1))) := by
    apply (hs i).congr
    intro n
    change |∫ z, g z * ((ε n/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε n/2) z-hcirc ω 1 0)) -
      (ε n)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε n) z-hcirc ω 1 0))) ∂(μ i)| = _
    rw [← hstep n]
    change |∫ z, g z * (D (n+1) z - D n z) ∂(μ i)| = _
    simp_rw [mul_sub]
    rw [integral_sub (hint (n+1)) (hint n), Real.dist_eq, abs_sub_comm]
  exact cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hdist)

end HarmonicBalls
