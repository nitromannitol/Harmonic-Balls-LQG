import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability
import LatticeProb.Prob.SummableIncrementsL1

/-! # Annular clocks at Brownian exit

The dyadic annular clocks converge almost surely and in L¹ under the Brownian
law at the exit of a bounded open domain, for almost every field.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Filter Set HarmonicBalls.Section6
open scoped NNReal ENNReal Topology ZeroAtInfty

namespace HarmonicBalls

/-- Actual annular dyadic exit clocks converge almost surely and in L¹. -/
theorem ae_exists_annular_clock_exit_L1_limit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ ω ∂P, ∃ L : ContinuousPath ℂ → ℝ,
      Integrable L (planarBrownianMotion x) ∧
      (∀ᵐ b ∂planarBrownianMotion x, Tendsto (fun k : ℕ =>
        ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale k)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
            (b s.toNNReal)) atTop (𝓝 (L b))) ∧
      Tendsto (fun k : ℕ => ∫ b, |(∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale k)^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
            (b s.toNNReal)) - L b| ∂planarBrownianMotion x) atTop (𝓝 0) := by
  obtain ⟨N, hsum⟩ := ae_summable_brownian_annular_exit_increments hh hγ0 hγ2 α x hδ hD hDb
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hsum, hcont, ae_recentered_inserted_circle_average hh α,
    ae_integrable_annular_clock_exit hh hD hDb γ α δ x,
    ae_uniformIntegrable_annular_clock_exit hh hγ0 hγ2 α x hδ hD hDb] with ω hsum hcont hrec hint hui
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let Z : ℕ → ℂ → ℝ := fun k z => (dyadicScale k)^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)
  let Y : ℕ → ContinuousPath ℂ → ℝ := fun k b =>
    ∫ s in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal, A.indicator (Z k) (b s.toNNReal)
  have hc (k : ℕ) : Continuous (Z k) := by
    have hr := dyadicScale_pos k
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
        fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      exact (hrec _ z hr).symm
    have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact ((hcont _ hr).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
  have hYi : ∀ k, Integrable (Y k) (planarBrownianMotion x) := hint
  have hs : Summable (fun k => ∫ b, |Y (k+1) b - Y k b| ∂planarBrownianMotion x) := by
    let f : ℕ → ℝ := fun k => ∫ b, ‖∫ t in (0 : ℝ)..(ContinuousPath.exitTime D b).toReal,
        A.indicator (fun z => (dyadicScale k / 2)^(γ^2/2) *
          Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k / 2) z) -
          (dyadicScale k)^(γ^2/2) *
          Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z))
          (b t.toNNReal)‖ ∂planarBrownianMotion x
    change Summable (fun k => f (k+N)) at hsum
    have hs' : Summable f := (summable_nat_add_iff N).1 hsum
    apply hs'.congr
    intro k
    apply integral_congr_ae
    filter_upwards with b
    have hscale : dyadicScale (k+1) = dyadicScale k / 2 := by
      simp only [dyadicScale, pow_succ]
      ring
    have hi1 := intervalIntegrable_annular_density (Z (k+1)) (hc (k+1)) δ b 0 (ContinuousPath.exitTime D b).toReal
    have hi0 := intervalIntegrable_annular_density (Z k) (hc k) δ b 0 (ContinuousPath.exitTime D b).toReal
    change ‖_‖ = |Y (k+1) b - Y k b|
    rw [← Real.norm_eq_abs, show Y (k+1) b - Y k b = _ from (intervalIntegral.integral_sub hi1 hi0).symm]
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [A, Z, Set.indicator_apply]
    split_ifs <;> simp [hscale]
  have hd : ∀ k, Integrable (fun b => Y (k+1) b - Y k b) (planarBrownianMotion x) :=
    fun k => (hYi (k+1)).sub (hYi k)
  have ha := LatticeProb.SummableIncrements.ae_exists_tendsto_of_summable_integral_abs_sub hd hs
  let L : ContinuousPath ℂ → ℝ := fun b => limUnder atTop (fun k => Y k b)
  have hL : ∀ᵐ b ∂planarBrownianMotion x, Tendsto (fun k => Y k b) atTop (𝓝 (L b)) := by
    filter_upwards [ha] with b hb
    exact tendsto_nhds_limUnder hb
  refine ⟨L, ?_, hL, ?_⟩
  · exact hui.integrable_of_ae_tendsto hL
  · exact LatticeProb.SummableIncrements.tendsto_integral_abs_sub_of_integral_abs_sub_le
      (fun k => (hYi k).aestronglyMeasurable) hd (fun _ => le_rfl) hs hL

end HarmonicBalls
