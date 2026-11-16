import HarmonicBalls.Proofs.Potential.LQGFineScaleHalfMesh
import LatticeProb.Gauss.CircleAverageRadialBrownian

/-! # Radial circle-average tails on spatial grids

Gaussian radial tails remain summable over exponentially growing finite grids.
-/

noncomputable section
open MeasureTheory Filter Set Metric LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- Gaussian decay dominates any exponential growth in a discrete index. -/
theorem summable_pow_mul_exp_neg_sq {A c : ℝ} (hA : 0 < A) (hc : 0 < c) :
    Summable fun n : ℕ => A ^ n * Real.exp (-c * (n : ℝ) ^ 2) := by
  let a := Real.log A
  let M := Real.exp (a ^ 2 / (2 * c))
  let q := Real.exp (-c / 2)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  have hsum := (summable_geometric_of_lt_one hq hq1).mul_left M
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
  have hx : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
      have hn : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
      nlinarith
  have hb : a * (n : ℝ) - c / 2 * (n : ℝ) ^ 2 ≤ a ^ 2 / (2 * c) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * c)).2
    nlinarith [sq_nonneg (c * (n : ℝ) - a)]
  have he : a * (n : ℝ) - c * (n : ℝ) ^ 2 ≤
      a ^ 2 / (2 * c) + (-c / 2) * (n : ℝ) := by
    nlinarith
  calc
    A ^ n * Real.exp (-c * (n : ℝ) ^ 2) =
        Real.exp (a * (n : ℝ) - c * (n : ℝ) ^ 2) := by
      have hAn : A ^ n = Real.exp (a * (n : ℝ)) := by
        dsimp [a]
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log hA]
      rw [hAn, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (a ^ 2 / (2 * c) + (-c / 2) * (n : ℝ)) :=
      Real.exp_le_exp.mpr he
    _ = M * q ^ n := by
      dsimp [M, q]
      rw [Real.exp_add, mul_comm (-c / 2) (n : ℝ), Real.exp_nat_mul]


/-- Gaussian radial tails give simultaneous eventual control at all points of
any spatial grids whose cardinalities have at most exponential growth. -/
theorem ae_eventually_grid_radial_oscillation
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {δ A B : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hB : 0 ≤ B)
    (S : ℕ → Finset ℂ) (hS : ∀ n, ((S n).card : ℝ) ≤ B * A ^ n) :
    ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ∀ z ∈ S n, ∀ s,
      LatticeProb.LQG.dyadicScale n / 2 ≤ s → s ≤ LatticeProb.LQG.dyadicScale n →
      |hcirc ω s z - hcirc ω (LatticeProb.LQG.dyadicScale n) z| ≤ δ * (n + 1) := by
  let c : ℝ := δ ^ 2 / (2 * Real.log 2)
  have hc : 0 < c := by dsimp [c]; positivity
  let E : ℕ → Set Ω := fun n => ⋃ z ∈ S n,
    {ω | ∃ s ∈ Icc (LatticeProb.LQG.dyadicScale n / 2) (LatticeProb.LQG.dyadicScale n),
      δ * (n + 1) < |hcirc ω s z - hcirc ω (LatticeProb.LQG.dyadicScale n) z|}
  have hpoint : ∀ n z, P {ω | ∃ s ∈ Icc
      (LatticeProb.LQG.dyadicScale n / 2) (LatticeProb.LQG.dyadicScale n),
      δ * (n + 1) < |hcirc ω s z - hcirc ω (LatticeProb.LQG.dyadicScale n) z|} ≤
        ENNReal.ofReal (2 * Real.exp (-c * (n : ℝ) ^ 2)) := by
    intro n z
    have hd : 0 < LatticeProb.LQG.dyadicScale n := by
      unfold LatticeProb.LQG.dyadicScale
      positivity
    have hT : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hth : 0 < δ * ((n : ℝ) + 1) := by positivity
    have h := hh.measure_exists_circle_sub_ge_le hd z hT hth
    have he : LatticeProb.LQG.dyadicScale n * Real.exp (-Real.log 2) =
        LatticeProb.LQG.dyadicScale n / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      ring
    rw [he] at h
    refine (measure_mono (fun ω hω => ?_)).trans (h.trans ?_)
    · obtain ⟨s, hs, hlt⟩ := hω
      exact ⟨s, hs, hlt.le⟩
    · rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      gcongr
      dsimp [c]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have hm : (n : ℝ) ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      have hp := mul_le_mul_of_nonneg_left hm (show 0 ≤ δ ^ 2 / (2 * Real.log 2) by positivity)
      have heq : (δ * ((n : ℝ) + 1)) ^ 2 / (2 * Real.log 2) =
          (δ ^ 2 / (2 * Real.log 2)) * ((n : ℝ) + 1) ^ 2 := by ring
      rw [heq]
      linarith
  have hsum : Summable fun n : ℕ => (2 * B) * (A ^ n * Real.exp (-c * (n : ℝ) ^ 2)) :=
    (summable_pow_mul_exp_neg_sq hA hc).mul_left _
  have hmeasure : ∀ n, P (E n) ≤ ENNReal.ofReal
      ((2 * B) * (A ^ n * Real.exp (-c * (n : ℝ) ^ 2))) := by
    intro n
    calc
      P (E n) ≤ ∑ z ∈ S n, ENNReal.ofReal (2 * Real.exp (-c * (n : ℝ) ^ 2)) :=
        (measure_biUnion_finset_le _ _).trans (Finset.sum_le_sum (fun z _ => hpoint n z))
      _ = ENNReal.ofReal (((S n).card : ℝ) * (2 * Real.exp (-c * (n : ℝ) ^ 2))) := by
        rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
          ← ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal ((2 * B) * (A ^ n * Real.exp (-c * (n : ℝ) ^ 2))) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [mul_le_mul_of_nonneg_right (hS n) (Real.exp_pos (-c * (n : ℝ) ^ 2)).le]
  have hfin : ∑' n, P (E n) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hmeasure)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with n hn z hz s hs1 hs2
  by_contra h
  apply hn
  simp only [E, mem_iUnion, mem_ofPred_eq]
  exact ⟨z, hz, s, ⟨hs1, hs2⟩, lt_of_not_ge h⟩

end HarmonicBalls

