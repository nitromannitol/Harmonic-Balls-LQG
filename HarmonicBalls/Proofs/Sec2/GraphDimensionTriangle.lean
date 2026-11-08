import HarmonicBalls.Proofs.Sec2.GraphDistanceTriangle
import HarmonicBalls.Proofs.Sec2.GraphDimensionScaleInterpolation

/-!
# Triangle inequality for graph-distance dimensions

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

/-- Reversing the endpoints preserves the graph-distance dimension. -/
theorem IsLiouvilleGraphDimension.symm {μ : Measure ℂ} {z w : ℂ} {d : ℝ}
    (h : IsLiouvilleGraphDimension μ z w d) : IsLiouvilleGraphDimension μ w z d := by
  have he : liouvilleGraphExponent μ w z = liouvilleGraphExponent μ z w := by
    funext n
    simp only [liouvilleGraphExponent, liouvilleGraphDistance_symm μ _ w z]
  refine ⟨h.1, ?_, ?_⟩
  · simpa only [liouvilleGraphDistance_symm μ _ w z] using h.2.1
  · rw [he]
    exact h.2.2

/-- The dimension between two endpoints is at least the smaller of the two
dimensions through an intermediate point. -/
theorem IsLiouvilleGraphDimension.min_le {μ : Measure ℂ} {z v w : ℂ} {d₁ d₂ d₃ : ℝ}
    (h₁ : IsLiouvilleGraphDimension μ z v d₁)
    (h₂ : IsLiouvilleGraphDimension μ v w d₂)
    (h₃ : IsLiouvilleGraphDimension μ z w d₃) : min d₁ d₂ ≤ d₃ := by
  have hlim : Tendsto (fun n : ℕ =>
      max (liouvilleGraphExponent μ z v n) (liouvilleGraphExponent μ v w n) + 1 / (n : ℝ))
      atTop (𝓝 (max (1 / d₁) (1 / d₂))) := by
    simpa only [add_zero] using (h₁.2.2.max h₂.2.2).add
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have hle : 1 / d₃ ≤ max (1 / d₁) (1 / d₂) := by
    apply le_of_tendsto_of_tendsto h₃.2.2 hlim
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hf₁ := h₁.graphDistance_ne_top (dyadicScale_pos n)
    have hf₂ := h₂.graphDistance_ne_top (dyadicScale_pos n)
    have hf₃ := h₃.graphDistance_ne_top (dyadicScale_pos n)
    have hnat := ENat.toNat_le_toNat (liouvilleGraphDistance_triangle μ (dyadicScale n) z v w)
      (WithTop.add_ne_top.mpr ⟨hf₁, hf₂⟩)
    rw [ENat.toNat_add hf₁ hf₂] at hnat
    have hpos : 0 < (liouvilleGraphDistance μ (dyadicScale n) z w).toNat := by
      have hh := ENat.toNat_le_toNat (one_le_liouvilleGraphDistance μ (dyadicScale n) z w) hf₃
      simp only [ENat.toNat_one] at hh
      omega
    have hbound : (liouvilleGraphDistance μ (dyadicScale n) z w).toNat ≤
        2 * max (liouvilleGraphDistance μ (dyadicScale n) z v).toNat
          (liouvilleGraphDistance μ (dyadicScale n) v w).toNat := by omega
    have hlog := Real.log_le_log (show (0 : ℝ) < _ by exact_mod_cast hpos)
      (show ((liouvilleGraphDistance μ (dyadicScale n) z w).toNat : ℝ) ≤
        2 * (max (liouvilleGraphDistance μ (dyadicScale n) z v).toNat
          (liouvilleGraphDistance μ (dyadicScale n) v w).toNat : ℕ) by exact_mod_cast hbound)
    have hmaxpos : (0 : ℝ) < (max (liouvilleGraphDistance μ (dyadicScale n) z v).toNat
          (liouvilleGraphDistance μ (dyadicScale n) v w).toNat : ℕ) := by
      have hh : 0 < max (liouvilleGraphDistance μ (dyadicScale n) z v).toNat
          (liouvilleGraphDistance μ (dyadicScale n) v w).toNat := by omega
      exact_mod_cast hh
    rw [Real.log_mul (by norm_num) (ne_of_gt hmaxpos), Nat.cast_max] at hlog
    have hlogmax : Real.log (max ((liouvilleGraphDistance μ (dyadicScale n) z v).toNat : ℝ)
        ((liouvilleGraphDistance μ (dyadicScale n) v w).toNat : ℝ)) ≤
        max (Real.log (liouvilleGraphDistance μ (dyadicScale n) z v).toNat)
          (Real.log (liouvilleGraphDistance μ (dyadicScale n) v w).toNat) := by
      rcases le_total ((liouvilleGraphDistance μ (dyadicScale n) z v).toNat : ℝ)
          ((liouvilleGraphDistance μ (dyadicScale n) v w).toNat : ℝ) with ha | ha
      · rw [max_eq_right ha]; exact le_max_right _ _
      · rw [max_eq_left ha]; exact le_max_left _ _
    have hlog := hlog.trans (add_le_add_right hlogmax _)
    have hden : 0 < (n : ℝ) * Real.log 2 :=
      mul_pos (by exact_mod_cast hn) (Real.log_pos (by norm_num))
    have hd := div_le_div_of_nonneg_right hlog hden.le
    dsimp only [liouvilleGraphExponent]
    rw [add_div, ← max_div_div_right hden.le _ _] at hd
    have heq : Real.log 2 / ((n : ℝ) * Real.log 2) = 1 / (n : ℝ) := by
      field_simp
    rw [heq] at hd
    linarith
  by_cases h : d₁ ≤ d₂
  · rw [min_eq_left h]
    have hi : 1 / d₂ ≤ 1 / d₁ := by
      simpa only [one_div] using (inv_le_inv₀ h₂.1 h₁.1).2 h
    rw [max_eq_left hi] at hle
    exact (inv_le_inv₀ h₃.1 h₁.1).1 (by simpa only [one_div] using hle)
  · have h' : d₂ ≤ d₁ := le_of_not_ge h
    rw [min_eq_right h']
    have hi : 1 / d₁ ≤ 1 / d₂ := by
      simpa only [one_div] using (inv_le_inv₀ h₁.1 h₂.1).2 h'
    rw [max_eq_right hi] at hle
    exact (inv_le_inv₀ h₃.1 h₂.1).1 (by simpa only [one_div] using hle)

#print axioms IsLiouvilleGraphDimension.symm
#print axioms IsLiouvilleGraphDimension.min_le

end HarmonicBalls
