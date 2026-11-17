import HarmonicBalls.Proofs.Potential.LQGClockAnnularContinuumSmoothing
import LatticeProb.Prob.ExpFamily

/-! # Nearby-radius annular clock densities

A radial modulus of the inserted field controls the corresponding normalized
exponential densities.
-/

open MeasureTheory Filter LatticeProb.LQG
open scoped Topology

namespace HarmonicBalls

private theorem abs_log_sub_le_of_lower {s t d : ℝ} (hd : 0 < d)
    (hs : d ≤ s) (ht : d ≤ t) :
    |Real.log s - Real.log t| ≤ |s - t| / d := by
  have hs0 : 0 < s := hd.trans_le hs
  have ht0 : 0 < t := hd.trans_le ht
  have hst : Real.log s - Real.log t ≤ (s - t) / t := by
    have h := Real.log_le_sub_one_of_pos (div_pos hs0 ht0)
    rw [Real.log_div hs0.ne' ht0.ne'] at h
    convert h using 1; field_simp
  have hts : Real.log t - Real.log s ≤ (t - s) / s := by
    have h := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
    rw [Real.log_div ht0.ne' hs0.ne'] at h
    convert h using 1; field_simp
  rcases le_total t s with h | h
  · rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hq : (s - t) / t ≤ (s - t) / d :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr h) hd ht
    apply abs_le.mpr
    constructor
    · have : Real.log t ≤ Real.log s := Real.log_le_log ht0 h
      linarith [div_nonneg (sub_nonneg.mpr h) hd.le]
    · exact hst.trans hq
  · rw [abs_of_nonpos (sub_nonpos.mpr h)]
    have hq : (t - s) / s ≤ (t - s) / d :=
      div_le_div_of_nonneg_left (sub_nonneg.mpr h) hd hs
    apply abs_le.mpr
    constructor
    · have he : -(s - t) / d = (t - s) / d := by ring
      rw [he]
      linarith [hts.trans hq]
    · have : Real.log s ≤ Real.log t := Real.log_le_log hs0 h
      have : 0 ≤ -(s - t) / d := div_nonneg (by linarith) hd.le
      linarith

/-- A bound on the logarithmic difference of two positive-scale densities
controls their relative difference. -/
theorem abs_normalized_exp_sub_le {s t γ x y B : ℝ}
    (hs : 0 < s) (ht : 0 < t) (hB : 0 ≤ B)
    (h : |(Real.log s - Real.log t) * (γ ^ 2 / 2) + γ * (x - y)| ≤ B) :
    |s ^ (γ ^ 2 / 2) * Real.exp (γ * x) -
      t ^ (γ ^ 2 / 2) * Real.exp (γ * y)| ≤
      B * Real.exp B * (t ^ (γ ^ 2 / 2) * Real.exp (γ * y)) := by
  let u := (Real.log s - Real.log t) * (γ ^ 2 / 2) + γ * (x - y)
  let v := Real.log t * (γ ^ 2 / 2) + γ * y
  have heq : s ^ (γ ^ 2 / 2) * Real.exp (γ * x) = Real.exp u * Real.exp v := by
    rw [Real.rpow_def_of_pos hs, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp [u, v]
    ring
  have heq' : t ^ (γ ^ 2 / 2) * Real.exp (γ * y) = Real.exp v := by
    rw [Real.rpow_def_of_pos ht, ← Real.exp_add]
  have hu : |u| ≤ B := h
  have hexp : |Real.exp u - 1| ≤ B * Real.exp B := by
    have hh := LatticeProb.abs_exp_sub_exp_le u 0
    simp only [Real.exp_zero, sub_zero] at hh
    calc
      _ ≤ |u| * Real.exp (max u 0) := hh
      _ ≤ B * Real.exp B := by
        gcongr
        exact max_le (le_trans (le_abs_self u) hu) hB
  rw [heq, heq']
  have hf : Real.exp u * Real.exp v - Real.exp v = (Real.exp u - 1) * Real.exp v := by ring
  rw [hf, abs_mul, abs_of_pos (Real.exp_pos v)]
  exact mul_le_mul_of_nonneg_right hexp (Real.exp_pos v).le

/-- Fine radial field regularity gives a uniform relative estimate for the
normalized inserted density on a positive-cutoff annulus. -/
theorem ae_eventually_annular_density_radial_difference_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ z : ℂ, δ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ∀ s t : ℝ,
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        dyadicScale k / 2 ≤ t → t ≤ dyadicScale k →
        |s - t| < dyadicScale k * dyadicScale k ^ a →
        let B := |γ| * dyadicScale k ^ β + γ ^ 2 * dyadicScale k ^ a
        |s ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z) -
          t ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z)| ≤
          B * Real.exp B * (t ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z)) := by
  obtain ⟨β, hβ, hmod⟩ := ae_eventually_inserted_circle_radial_modulus hh α hδ ha
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hmod] with ω hω
  filter_upwards [hω] with k hk z hz hz' s t hs1 hs2 ht1 ht2 hst
  have hd : 0 < dyadicScale k := dyadicScale_pos k
  have hs : 0 < s := by linarith
  have ht : 0 < t := by linarith
  have hlog : |Real.log s - Real.log t| ≤ 2 * dyadicScale k ^ a := by
    calc
      _ ≤ |s - t| / (dyadicScale k / 2) :=
        abs_log_sub_le_of_lower (by positivity) hs1 ht1
      _ ≤ 2 * dyadicScale k ^ a := by
        rw [div_le_iff₀ (by positivity : 0 < dyadicScale k / 2)]
        nlinarith [hst.le]
  have hf := hk z hz hz' s t hs1 hs2 ht1 ht2 hst
  let B : ℝ := |γ| * dyadicScale k ^ β + γ ^ 2 * dyadicScale k ^ a
  have hB : 0 ≤ B := by dsimp [B]; positivity
  apply abs_normalized_exp_sub_le hs ht hB
  calc
    _ ≤ |Real.log s - Real.log t| * |γ ^ 2 / 2| +
        |γ| * |LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z -
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z| := by
      have htriangle := abs_add_le
        ((Real.log s - Real.log t) * (γ ^ 2 / 2))
        (γ * (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z -
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) t z))
      rw [abs_mul, abs_mul] at htriangle
      exact htriangle
    _ ≤ B := by
      have hγ : 0 ≤ γ ^ 2 / 2 := by positivity
      rw [abs_of_nonneg hγ]
      dsimp [B]
      nlinarith [mul_le_mul_of_nonneg_right hlog hγ,
        mul_le_mul_of_nonneg_left hf (abs_nonneg γ)]

end HarmonicBalls
