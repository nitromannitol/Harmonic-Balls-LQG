import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridRadiusIncrement
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability

/-! # Annular clock comparison at nearby radii

A relative density estimate transfers to stopped occupation integrals.
-/

open MeasureTheory Set MarkovProcess Filter
open scoped Topology NNReal ENNReal

namespace HarmonicBalls

/-- A relative estimate on continuous annular densities transfers to their
occupation integrals over every bounded nonnegative time interval. -/
theorem abs_annular_occupation_sub_le (f g : ℂ → ℝ) (hf : Continuous f)
    (hg : Continuous g) (δ C : ℝ)
    (hfg : ∀ z, δ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → |f z - g z| ≤ C * g z)
    (b : ContinuousPath ℂ) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0 : ℝ)..T, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b t.toNNReal)) -
      (∫ t in (0 : ℝ)..T, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator g (b t.toNNReal))| ≤
    C * (∫ t in (0 : ℝ)..T, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator g (b t.toNNReal)) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let F : ℝ → ℝ := fun t => A.indicator f (b t.toNNReal)
  let G : ℝ → ℝ := fun t => A.indicator g (b t.toNNReal)
  have hF : IntervalIntegrable F volume 0 T := intervalIntegrable_annular_density f hf δ b 0 T
  have hG : IntervalIntegrable G volume 0 T := intervalIntegrable_annular_density g hg δ b 0 T
  have hp (t : ℝ) : |F t - G t| ≤ C * G t := by
    dsimp [F, G]
    by_cases hz : b t.toNNReal ∈ A
    · simp only [Set.indicator_of_mem hz]
      exact hfg _ hz.1 hz.2
    · simp [Set.indicator_of_notMem hz]
  change |(∫ t in (0 : ℝ)..T, F t) - ∫ t in (0 : ℝ)..T, G t| ≤ C * ∫ t in (0 : ℝ)..T, G t
  rw [← intervalIntegral.integral_sub hF hG]
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, |F t - G t| := intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ t in (0 : ℝ)..T, C * G t := by
      apply intervalIntegral.integral_mono_on hT (hF.sub hG).abs (hG.const_mul C)
      exact fun t _ => hp t
    _ = _ := intervalIntegral.integral_const_mul C G

private theorem continuous_inserted_density_at_radius (hcirc : ℝ → ℂ → ℝ)
    (γ α r : ℝ) (hr : 0 < r) (hc : Continuous (hcirc r))
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
    exact (hc.sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))

/-- The nearby-radius density modulus controls actual stopped annular clocks
simultaneously for every path and finite time. -/
theorem ae_eventually_annular_stopped_occupation_radial_difference_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) (D : Set ℂ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ (b : ContinuousPath ℂ) (t : ℝ≥0) (s r : ℝ),
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        dyadicScale k / 2 ≤ r → r ≤ dyadicScale k →
        |s - r| < dyadicScale k * dyadicScale k ^ a →
        let B := |γ| * dyadicScale k ^ β + γ ^ 2 * dyadicScale k ^ a
        |(∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            s ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z)) (b u.toNNReal)) -
         (∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            r ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) (b u.toNNReal))| ≤
          B * Real.exp B * (∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            r ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) (b u.toNNReal)) := by
  obtain ⟨β, hβ, hmod⟩ := ae_eventually_annular_density_radial_difference_le hh α γ hδ ha
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hmod, hHae, ae_recentered_inserted_circle_average hh α] with ω hω hc hrec
  have hcont : ∀ r, 0 < r → Continuous (hcirc ω r) := by
    intro r hr
    rw [← funext (hc r)]
    exact hHc ω r hr
  filter_upwards [hω] with k hk b t s r hs1 hs2 hr1 hr2 hsr
  have hs : 0 < s := (half_pos (dyadicScale_pos k)).trans_le hs1
  have hr : 0 < r := (half_pos (dyadicScale_pos k)).trans_le hr1
  apply abs_annular_occupation_sub_le _ _
    (continuous_inserted_density_at_radius _ γ α s hs (hcont s hs) (fun z => hrec s z hs))
    (continuous_inserted_density_at_radius _ γ α r hr (hcont r hr) (fun z => hrec r z hr))
  · exact fun z hz hz' => hk z hz hz' s r hs1 hs2 hr1 hr2 hsr
  · exact le_min t.coe_nonneg ENNReal.toReal_nonneg

end HarmonicBalls
