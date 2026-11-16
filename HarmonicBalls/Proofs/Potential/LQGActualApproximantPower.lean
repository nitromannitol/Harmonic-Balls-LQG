import HarmonicBalls.Proofs.Potential.LQGOrdinaryCircleBridge
import HarmonicBalls.Proofs.Potential.LQGApproxAllCenterPower
import LatticeProb.LQG.CompactBallApproximantPower

/-! # Compact-center power bounds for circle-average approximations

The ordinary and singular dyadic approximations have simultaneous positive-power
bounds on small balls with centers in a compact disk.
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- The ordinary approximations have a common compact-center ball power bound. -/
theorem IsWholePlaneGFF.ae_ordinary_approximant_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (R : ℝ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᵐ ω ∂P, ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        lqgApprox γ (hcirc ω) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (C * s ^ κ) := by
  obtain ⟨H, hH, hHm, heq⟩ := hh.exists_measurable_gff_circle_average
  obtain ⟨p, q, hp, hpq, hq⟩ := exists_lqg_moment_parameters hγ hγ2
  obtain ⟨κ, hκ, hbound⟩ :=
    LatticeProb.LQG.ae_exists_compact_center_ball_approximant_power_bound
      hH hHm hγ hγ2 hp hpq hq (closedBall (0 : ℂ) R) (isCompact_closedBall 0 R)
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [heq, hbound] with ω heqω hboundω
  obtain ⟨C, hC, hCbound⟩ := hboundω
  apply lqgApprox_ball_power_transfer_of_circle_eq hC heqω
  intro z hz s hs hs1 k
  have h := hCbound z (by simpa [mem_closedBall, dist_zero_right] using hz) s hs hs1 k
  simpa [lqgApprox, dyadicScale, LatticeProb.LQG.lqgApprox,
    QuantumZipper.radius] using h

/-- The singular approximations have a common compact-center small-ball power bound. -/
theorem IsWholePlaneGFF.ae_singular_approximant_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) (R : ℝ) :
    ∀ᵐ ω ∂P, ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
      ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (C * s ^ β) := by
  obtain ⟨κ, hκ, hord⟩ := hh.ae_ordinary_approximant_ball_power hγ hγ2 R
  filter_upwards [hord, ae_singular_approximant_small_ball_power_of_positive_ordinary_power
    hh hγ hγ2 hαQ (δ := 1) (r := 1 / 4) (ρ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) R] with ω hordω hsing
  obtain ⟨C, hC, hbound⟩ := hordω
  exact hsing C κ hC hκ hbound

/-- One event gives a small-ball power bound on every compact disk. -/
theorem IsWholePlaneGFF.ae_singular_approximant_ball_power_all_disks
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C β r₀ : ℝ, 0 < C ∧ 0 < β ∧ 0 < r₀ ∧
      ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R → ∀ s : ℝ, 0 < s → s ≤ r₀ →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (C * s ^ β) := by
  filter_upwards [ae_all_iff.mpr (fun n : ℕ =>
    hh.ae_singular_approximant_ball_power hγ hγ2 hαQ n)] with ω hω R
  obtain ⟨n, hn⟩ := exists_nat_ge R
  obtain ⟨C, β, r₀, hC, hβ, hr₀, hbound⟩ := hω n
  refine ⟨C, β, r₀, hC, hβ, hr₀, ?_⟩
  intro k z hz s hs hsr
  exact hbound k z (hz.trans hn) s hs hsr

end HarmonicBalls
