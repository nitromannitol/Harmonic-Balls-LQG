import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Summability along good scales

The estimates are deterministic and allow unbounded gaps between good scales.
-/

namespace HarmonicBalls

open Filter
open scoped Topology

/-- A negative limiting exponential rate along scales growing at least linearly
implies summability. Division is total, so finitely many zero scales are allowed. -/
theorem summable_exp_of_scale_rate {n : ℕ → ℕ} {e : ℕ → ℝ} {a : ℝ}
    (hn : ∀ i, i ≤ n i) (ha : a < 0)
    (he : Tendsto (fun i => e i / (n i : ℝ)) atTop (𝓝 a)) :
    Summable (fun i => Real.exp (e i)) := by
  have hs : Summable (fun i : ℕ => Real.exp (a / 2) ^ i) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (by linarith))
  apply Summable.of_norm_bounded_eventually_nat hs
  have hb : ∀ᶠ i in atTop, e i / (n i : ℝ) < a / 2 :=
    he.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hb, eventually_ge_atTop 1] with i hi hi1
  have hnpos : 0 < (n i : ℝ) := by exact_mod_cast (lt_of_lt_of_le hi1 (hn i))
  have hni : (i : ℝ) ≤ n i := by exact_mod_cast hn i
  have he' : e i ≤ (a / 2) * n i := by
    exact (div_lt_iff₀ hnpos).mp hi |>.le
  have hbound : e i ≤ (a / 2) * i := by nlinarith
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hbound

/-- Good scales tend to infinity as soon as the `i`-th scale is at least `i`. -/
theorem tendsto_good_scales_atTop {n : ℕ → ℕ} (hn : ∀ i, i ≤ n i) :
    Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id

/-- The original scale lengths appearing in the good-scale construction. -/
noncomputable def goodScaleLength (M ξ Q : ℝ) (n : ℕ → ℕ) (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  M * (2 : ℝ) ^ (-ξ * Q * (n i : ℝ)) * Real.exp (ξ * b (n i))

/-- The exact upper bound for the singularly weighted stopped segment. -/
noncomputable def goodScaleWeightedLength (M ξ Q α : ℝ) (n : ℕ → ℕ)
    (b : ℕ → ℝ) (i : ℕ) : ℝ :=
  2 * goodScaleLength M ξ Q n b i *
    if 0 ≤ α then ((2 : ℝ) ^ (-(n (i + 1) : ℝ))) ^ (-α * ξ)
    else (2 * (2 : ℝ) ^ (-(n i : ℝ))) ^ (-α * ξ)

/-- Linear exponential rates remain summable after a sublinear error and a
second scale asymptotic to the first. -/
theorem summable_exp_good_scale {n m : ℕ → ℕ} {b : ℕ → ℝ} {κ τ ξ : ℝ}
    (hn : ∀ i, i ≤ n i) (hgap : τ < κ)
    (hb : Tendsto (fun j => b j / (j : ℝ)) atTop (𝓝 0))
    (hm : Tendsto (fun i => (m i : ℝ) / (n i : ℝ)) atTop (𝓝 1)) :
    Summable (fun i => Real.exp (-κ * (n i : ℝ) + ξ * b (n i) + τ * (m i : ℝ))) := by
  have hninf := tendsto_good_scales_atTop hn
  have hb' := hb.comp hninf
  have hlim : Tendsto (fun i => -κ + ξ * (b (n i) / (n i : ℝ)) +
      τ * ((m i : ℝ) / (n i : ℝ))) atTop (𝓝 (-κ + τ)) := by
    have h : Tendsto (fun i => -κ + ξ * (b (n i) / (n i : ℝ)) +
        τ * ((m i : ℝ) / (n i : ℝ))) atTop (𝓝 ((-κ + ξ * 0) + τ * 1)) :=
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hb')).add
        (tendsto_const_nhds.mul hm)
    simpa only [mul_zero, add_zero, mul_one] using h
  apply summable_exp_of_scale_rate hn (by linarith : -κ + τ < 0)
  apply hlim.congr'
  filter_upwards [hninf.eventually (eventually_ne_atTop 0)] with i hi
  have hn0 : (n i : ℝ) ≠ 0 := by exact_mod_cast hi
  field_simp

private theorem good_scale_self_ratio {n : ℕ → ℕ} (hn : ∀ i, i ≤ n i) :
    Tendsto (fun i => (n i : ℝ) / (n i : ℝ)) atTop (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(tendsto_good_scales_atTop hn).eventually (eventually_ne_atTop 0)] with i hi
  have hn0 : (n i : ℝ) ≠ 0 := by exact_mod_cast hi
  simp [hn0]

/-- The original lengths are summable for any sublinear errors. -/
theorem summable_goodScaleLength {M ξ Q : ℝ} {n : ℕ → ℕ} {b : ℕ → ℝ}
    (hξ : 0 < ξ) (hQ : 0 < Q) (hn : ∀ i, i ≤ n i)
    (hb : Tendsto (fun j => b j / (j : ℝ)) atTop (𝓝 0)) :
    Summable (goodScaleLength M ξ Q n b) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := summable_exp_good_scale (n := n) (m := n) (b := b)
    (κ := ξ * Q * Real.log 2) (τ := 0) (ξ := ξ) hn (by positivity) hb
    (good_scale_self_ratio hn)
  have heq : goodScaleLength M ξ Q n b = fun i =>
      M * Real.exp (-(ξ * Q * Real.log 2) * (n i : ℝ) + ξ * b (n i) +
        0 * (n i : ℝ)) := by
    funext i
    simp only [goodScaleLength, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      zero_mul, add_zero, Real.exp_add]
    have h : Real.log 2 * (-ξ * Q * (n i : ℝ)) =
        -(ξ * Q * Real.log 2) * (n i : ℝ) := by ring
    rw [h, mul_assoc]
  rw [heq]
  exact hs.mul_left M

/-- The stopped weighted lengths are summable for either sign of the insertion.
The ratio assumption is meaningful even if an initial scale is zero. -/
theorem summable_goodScaleWeightedLength {M ξ Q α : ℝ} {n : ℕ → ℕ} {b : ℕ → ℝ}
    (hξ : 0 < ξ) (_hQ : 0 < Q) (hαQ : α < Q)
    (hn : ∀ i, i ≤ n i)
    (hb : Tendsto (fun j => b j / (j : ℝ)) atTop (𝓝 0))
    (hnext : Tendsto (fun i => (n (i + 1) : ℝ) / (n i : ℝ)) atTop (𝓝 1)) :
    Summable (goodScaleWeightedLength M ξ Q α n b) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hgap : α * ξ * Real.log 2 < ξ * Q * Real.log 2 := by
    have h := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hαQ hξ) hlog
    nlinarith
  by_cases hα : 0 ≤ α
  · have hs := summable_exp_good_scale (n := n) (m := fun i => n (i + 1)) (b := b)
      (κ := ξ * Q * Real.log 2) (τ := α * ξ * Real.log 2) (ξ := ξ)
      hn hgap hb hnext
    have heq : goodScaleWeightedLength M ξ Q α n b = fun i =>
        (2 * M) * Real.exp (-(ξ * Q * Real.log 2) * (n i : ℝ) + ξ * b (n i) +
          (α * ξ * Real.log 2) * (n (i + 1) : ℝ)) := by
      funext i
      simp only [goodScaleWeightedLength, hα, ↓reduceIte, goodScaleLength,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos (Real.exp_pos _),
        Real.log_exp, Real.exp_add]
      have h : Real.log 2 * (-(n (i + 1) : ℝ)) * (-α * ξ) =
          α * ξ * Real.log 2 * (n (i + 1) : ℝ) := by ring
      rw [h]
      have h' : Real.log 2 * (-ξ * Q * (n i : ℝ)) =
          -(ξ * Q * Real.log 2) * (n i : ℝ) := by ring
      rw [h']
      ring
    rw [heq]
    exact hs.mul_left (2 * M)
  · have hs := summable_exp_good_scale (n := n) (m := n) (b := b)
      (κ := ξ * Q * Real.log 2) (τ := α * ξ * Real.log 2) (ξ := ξ)
      hn hgap hb (good_scale_self_ratio hn)
    have heq : goodScaleWeightedLength M ξ Q α n b = fun i =>
        (2 * M * Real.exp (-α * ξ * Real.log 2)) *
          Real.exp (-(ξ * Q * Real.log 2) * (n i : ℝ) + ξ * b (n i) +
            (α * ξ * Real.log 2) * (n i : ℝ)) := by
      funext i
      simp only [goodScaleWeightedLength, hα, ↓reduceIte, goodScaleLength]
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)]
      simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos (Real.exp_pos _),
        Real.log_exp, Real.exp_add]
      have h : Real.log 2 * (-(n i : ℝ)) * (-α * ξ) =
          α * ξ * Real.log 2 * (n i : ℝ) := by ring
      rw [h]
      have h' : Real.log 2 * (-ξ * Q * (n i : ℝ)) =
          -(ξ * Q * Real.log 2) * (n i : ℝ) := by ring
      rw [h']
      have h'' : Real.log 2 * (-α * ξ) = -α * ξ * Real.log 2 := by ring
      rw [h'']
      ring
    rw [heq]
    exact hs.mul_left (2 * M * Real.exp (-α * ξ * Real.log 2))


end HarmonicBalls
