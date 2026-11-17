import HarmonicBalls.Proofs.Potential.LQGCoarseSmoothingBallPower
import HarmonicBalls.Proofs.Potential.LQGApproxGreenTail

/-! # Singular approximants at the insertion

A geometric dyadic bound gives a continuum ball-power estimate at the origin.
-/

noncomputable section
open MeasureTheory Filter Metric Set

namespace HarmonicBalls

/-- Singular masses of sufficiently small origin-centered balls have a positive
power bound for every smoothing scale no larger than the ball radius. -/
theorem IsWholePlaneGFF.ae_singular_continuum_origin_ball_power
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∃ A r₀ : ℝ, 0 < A ∧ 0 < r₀ ∧
      ∀ r, 0 < r → r < r₀ → ∀ s, 0 < s → s ≤ r →
        lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 r) ≤
          ENNReal.ofReal (A * r ^ β) := by
  let β : ℝ := γ * (lqgQ γ - α) / 2
  let q : ℝ := Real.exp (-β * Real.log 2)
  let C : ℝ := Real.exp (γ * (|α| * Real.log 2)) / (1 - q)
  have hβ : 0 < β := by dsimp [β]; positivity
  have hq : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); nlinarith)
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  refine ⟨β, hβ, ?_⟩
  filter_upwards [ae_eventually_lqgApprox_fieldCircleAverage_ball_le_geometric hlp hγ hγ2 hαQ]
    with ω hω
  obtain ⟨N, hN⟩ := eventually_atTop.1 hω
  refine ⟨C * (2 : ℝ) ^ β, dyadicScale (N + 1), by positivity,
    by simp [dyadicScale], ?_⟩
  intro r hr hr₀ s hs hsr
  have hdN1 : dyadicScale N ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  have hdN : 0 < dyadicScale N := by simp [dyadicScale]
  have hnext : dyadicScale (N + 1) = dyadicScale N / 2 :=
    LatticeProb.LQG.dyadicScale_succ_eq_half N
  have hrN : r < dyadicScale N := by rw [hnext] at hr₀; linarith
  obtain ⟨k, hk1, hk2⟩ := LatticeProb.LQG.exists_dyadicScale_bracket hr (hrN.trans_le hdN1)
  have hkN : N ≤ k := by
    by_contra h
    have hle : k + 1 ≤ N := by omega
    have hmono := LatticeProb.LQG.dyadicScale_le_of_le hle
    change dyadicScale N ≤ dyadicScale (k + 1) at hmono
    change dyadicScale (k + 1) ≤ r at hk1
    linarith
  have hdk : 0 < dyadicScale k := by simp [dyadicScale]
  have hdkle : dyadicScale k ≤ 2 * r := by
    change LatticeProb.LQG.dyadicScale (k + 1) ≤ r at hk1
    rw [LatticeProb.LQG.dyadicScale_succ_eq_half] at hk1
    change dyadicScale k / 2 ≤ r at hk1
    linarith
  have hmass := hN k hkN s hs (hsr.trans_lt hk2)
  change lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 (dyadicScale k)) ≤
    ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
      (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ k /
        (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2))))) at hmass
  have heq : q ^ k = dyadicScale k ^ β := by
    rw [Real.rpow_def_of_pos hdk]
    unfold dyadicScale
    rw [Real.log_pow, Real.log_inv]
    dsimp [q]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hbound : C * dyadicScale k ^ β ≤ C * ((2 : ℝ) ^ β * r ^ β) := by
    have hp := Real.rpow_le_rpow hdk.le hdkle hβ.le
    rw [Real.mul_rpow (by norm_num) hr.le] at hp
    gcongr
  have hmass' : lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 (dyadicScale k)) ≤
      ENNReal.ofReal (C * dyadicScale k ^ β) := by
    convert hmass using 1
    rw [← heq]
    dsimp [C, q, β]
    congr 1
    ring
  calc
    _ ≤ lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 (dyadicScale k)) :=
      measure_mono (ball_subset_ball hk2.le)
    _ ≤ ENNReal.ofReal (C * dyadicScale k ^ β) := hmass'
    _ ≤ ENNReal.ofReal (C * ((2 : ℝ) ^ β * r ^ β)) := ENNReal.ofReal_le_ofReal hbound
    _ = ENNReal.ofReal (C * (2 : ℝ) ^ β * r ^ β) := by ring

end HarmonicBalls
