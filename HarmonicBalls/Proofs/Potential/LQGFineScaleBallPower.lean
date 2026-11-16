import HarmonicBalls.Proofs.Potential.LQGCompactCircleBound
import HarmonicBalls.Proofs.Potential.LQGActualApproximantPower

/-! # Fine-scale mass bounds on spatial grids

A fine-smoothing band comparison and dyadic mass bounds give a positive
power estimate simultaneously on the grid.
-/

noncomputable section
open MeasureTheory Filter Set Metric LatticeProb.LQG

namespace HarmonicBalls

/-- The ordinary mass at all sufficiently fine smoothing scales in each band
has a common positive-power bound on bounded spatial grids. -/
theorem IsWholePlaneGFF.ae_fine_scale_grid_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ R : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hR : 0 < R) :
    ∃ m : ℕ, ∃ S : ℕ → Finset ℂ,
      (∀ j x, x ∈ S j → ‖x‖ ≤ R + 1) ∧
      (∀ j z, z ∈ ball (0 : ℂ) R → ∃ x ∈ S j, dist z x < LatticeProb.LQG.dyadicScale j) ∧
      ∀ᵐ ω ∂P, ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ᶠ j in atTop,
        ∀ n, m * j ≤ n → ∀ x ∈ S j, ∀ t,
          LatticeProb.LQG.dyadicScale n / 2 ≤ t →
          t ≤ LatticeProb.LQG.dyadicScale n →
          LatticeProb.LQG.lqgApprox γ (hcirc ω) (LatticeProb.LQG.dyadicScale j * t)
              (ball x (LatticeProb.LQG.dyadicScale j)) ≤
            ENNReal.ofReal (C * LatticeProb.LQG.dyadicScale j ^ κ) := by
  obtain ⟨m, S, hS, hcover, hband⟩ := ae_fine_scale_ball_le_band hγ hγ2 hR
  obtain ⟨β, hβ, hdyad⟩ := hh.ae_ordinary_approximant_ball_power hγ hγ2 (R + 1)
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  refine ⟨m, S, hS, hcover, ?_⟩
  filter_upwards [hband P hC hcirc hlp, hdyad,
    hh.ae_compact_affine_circle_error_positive_power hγ hγ2] with ω hbandω hdyadω herrω
  obtain ⟨A, hA, hdyadω⟩ := hdyadω
  obtain ⟨B, η, hB, hη, herrω⟩ := herrω (R + 1)
  let K : ℝ := Real.exp (γ ^ 2 / 2 * Real.log 2 + γ)
  refine ⟨K * (A * (2 : ℝ) ^ β + B), min β η, by
    dsimp [K]; positivity, lt_min hβ hη, ?_⟩
  filter_upwards [hbandω, eventually_ge_atTop 2] with j hj hj2 n hn x hx t ht1 ht2
  let d := LatticeProb.LQG.dyadicScale j
  have hd : 0 < d := by unfold d LatticeProb.LQG.dyadicScale; positivity
  have hd1 : d ≤ 1 := by
    unfold d LatticeProb.LQG.dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hd2 : d * 2 ≤ 1 := by
    have hpow : LatticeProb.LQG.dyadicScale j ≤ LatticeProb.LQG.dyadicScale 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num [LatticeProb.LQG.dyadicScale] at hpow
    dsimp [d, LatticeProb.LQG.dyadicScale]
    norm_num
    linarith
  have he := herrω (j - 2) x (hS j x hx)
  have hidx : j - 2 + 2 = j := by omega
  rw [hidx] at he
  have ho := hdyadω (j + n) x (hS j x hx) (d * 2) (by positivity) hd2
  change LatticeProb.LQG.lqgApprox γ (hcirc ω)
    (LatticeProb.LQG.dyadicScale (j + n)) (ball x (d * 2)) ≤ _ at ho
  rw [LatticeProb.LQG.dyadicScale_add] at ho
  have hpow : (d * 2) ^ β = (2 : ℝ) ^ β * d ^ β := by
    rw [Real.mul_rpow hd.le (by norm_num)]
    ring
  rw [hpow] at ho
  have hb : d ^ β ≤ d ^ min β η := Real.rpow_le_rpow_of_exponent_ge hd hd1 (min_le_left _ _)
  have hc : d ^ η ≤ d ^ min β η := Real.rpow_le_rpow_of_exponent_ge hd hd1 (min_le_right _ _)
  have hreal : A * ((2 : ℝ) ^ β * d ^ β) + B * d ^ η ≤
      (A * (2 : ℝ) ^ β + B) * d ^ min β η := by
    have h1 := mul_le_mul_of_nonneg_left hb (show 0 ≤ A * (2 : ℝ) ^ β by positivity)
    have h2 := mul_le_mul_of_nonneg_left hc hB.le
    nlinarith
  have hsum : ENNReal.ofReal (A * ((2 : ℝ) ^ β * d ^ β)) +
      ENNReal.ofReal (B * d ^ η) ≤
        ENNReal.ofReal ((A * (2 : ℝ) ^ β + B) * d ^ min β η) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc
    _ ≤ ENNReal.ofReal K * (LatticeProb.LQG.lqgApprox γ (hcirc ω)
      (LatticeProb.LQG.dyadicScale j * LatticeProb.LQG.dyadicScale n) (ball x (d * 2)) +
      LQGDyadicScaling.dyadicFactor γ j (hcirc ω d x) *
        ENNReal.ofReal (Real.exp (γ * affineRecentredCircle (hcirc ω) d x 4 0))) :=
          hj n hn x hx t ht1 ht2
    _ ≤ ENNReal.ofReal K * (ENNReal.ofReal (A * ((2 : ℝ) ^ β * d ^ β)) +
        ENNReal.ofReal (B * d ^ η)) := by gcongr
    _ ≤ ENNReal.ofReal K *
        ENNReal.ofReal ((A * (2 : ℝ) ^ β + B) * d ^ min β η) := by gcongr
    _ = ENNReal.ofReal (K * (A * (2 : ℝ) ^ β + B) * d ^ min β η) := by
      rw [← ENNReal.ofReal_mul (show 0 ≤ K by dsimp [K]; positivity)]
      congr 1
      ring


/-- A half-mesh cover retains quadratic grid growth at the original scale. -/
theorem exists_bounded_half_mesh_grids (R : ℝ) (hR : 0 < R) :
    ∃ S : ℕ → Finset ℂ, ∀ j,
      ((S j).card : ℝ) ≤ (4 * (2 * R + 1) + 1) ^ 2 * (4 : ℝ) ^ j ∧
      (∀ x ∈ S j, ‖x‖ ≤ R + 1) ∧
      ∀ z ∈ ball (0 : ℂ) R, ∃ x ∈ S j,
        dist z x < LatticeProb.LQG.dyadicScale j / 2 := by
  obtain ⟨S, hS⟩ := exists_bounded_dyadic_ball_grids R hR
  refine ⟨fun j => S (j + 1), fun j => ⟨?_, (hS (j + 1)).2.1, ?_⟩⟩
  · have hcoeff : 4 * (4 * R + 1) ^ 2 ≤ (4 * (2 * R + 1) + 1) ^ 2 := by
      nlinarith
    calc
      ((S (j + 1)).card : ℝ) ≤ (4 * R + 1) ^ 2 * (4 : ℝ) ^ (j + 1) := (hS (j + 1)).1
      _ = (4 * (4 * R + 1) ^ 2) * (4 : ℝ) ^ j := by rw [pow_succ]; ring
      _ ≤ (4 * (2 * R + 1) + 1) ^ 2 * (4 : ℝ) ^ j := by gcongr
  · intro z hz
    obtain ⟨x, hx, hdist⟩ := (hS (j + 1)).2.2 z hz
    refine ⟨x, hx, ?_⟩
    simpa [LatticeProb.LQG.dyadicScale_succ_eq_half] using hdist

end HarmonicBalls
