import HarmonicBalls.Proofs.Sec2.GraphDimensionScaleInterpolation

/-!
# Mass normalization of Liouville graph distance

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- Scaling the measure changes the admissible mass threshold by the reciprocal factor. -/
theorem isLiouvilleGraphCover_smul_iff (μ : Measure ℂ) {c ε : ℝ} (hc : 0 < c)
    (_hε : 0 < ε) (z w : ℂ) (count : ℕ) :
    IsLiouvilleGraphCover (ENNReal.ofReal c • μ) ε z w count ↔
      IsLiouvilleGraphCover μ (ε / c) z w count := by
  have hc0 : ENNReal.ofReal c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hc)
  have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmass (s : Set ℂ) :
      (ENNReal.ofReal c • μ) s ≤ ENNReal.ofReal ε ↔
        μ s ≤ ENNReal.ofReal (ε / c) := by
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_div_of_pos hc]
    rw [mul_comm (ENNReal.ofReal c)]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hct)).symm
  unfold IsLiouvilleGraphCover
  simp only [hmass]

/-- Liouville graph distance under a positive finite normalization of the measure. -/
theorem liouvilleGraphDistance_smul (μ : Measure ℂ) {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) (z w : ℂ) :
    liouvilleGraphDistance (ENNReal.ofReal c • μ) ε z w =
      liouvilleGraphDistance μ (ε / c) z w := by
  unfold liouvilleGraphDistance
  congr 1
  ext n
  simp only [Set.mem_ofPred_eq, isLiouvilleGraphCover_smul_iff μ hc hε]

/-- A positive scaling preserves a graph-dimension exponent. -/
theorem IsLiouvilleGraphDimension.smul {μ : Measure ℂ} {z w : ℂ} {d c : ℝ}
    (h : IsLiouvilleGraphDimension μ z w d) (hc : 0 < c) :
    IsLiouvilleGraphDimension (ENNReal.ofReal c • μ) z w d := by
  have hscale : Tendsto (fun ε : ℝ => ε / c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    constructor
    · simpa using (((continuousAt_id.div_const c).tendsto : Tendsto (fun x : ℝ => x / c) (𝓝 0) (𝓝 (0 / c))).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact div_pos hε hc
  have hlog : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hratio : Tendsto (fun ε : ℝ => Real.log (ε / c)⁻¹ / Real.log ε⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have ht : Tendsto (fun ε : ℝ => 1 + Real.log c / Real.log ε⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa using (tendsto_const_nhds.add (tendsto_const_nhds.div_atTop hlog))
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin, hlog.eventually (Ioi_mem_atTop (0 : ℝ))] with ε hε hl
    have he : ε ≠ 0 := ne_of_gt hε
    have hl0 : Real.log ε⁻¹ ≠ 0 := ne_of_gt hl
    have hle : Real.log ε ≠ 0 := by simpa only [Real.log_inv, neg_ne_zero] using hl0
    rw [inv_div, Real.log_div (ne_of_gt hc) he, Real.log_inv]
    field_simp [hle]
    ring
  have hlim := (h.fullScale.comp hscale).mul hratio
  have hfinite : ∀ n : ℕ, liouvilleGraphDistance (ENNReal.ofReal c • μ)
      (dyadicScale n) z w ≠ ⊤ := by
    intro n
    rw [liouvilleGraphDistance_smul μ hc (dyadicScale_pos n)]
    exact h.graphDistance_ne_top (div_pos (dyadicScale_pos n) hc)
  have hfull : Tendsto (fun ε : ℝ =>
      Real.log (liouvilleGraphDistance (ENNReal.ofReal c • μ) ε z w).toNat /
        Real.log ε⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 (1 / d)) := by
    have hlim' : Tendsto (fun ε : ℝ =>
        (Real.log (liouvilleGraphDistance μ (ε / c) z w).toNat /
          Real.log (ε / c)⁻¹) * (Real.log (ε / c)⁻¹ / Real.log ε⁻¹))
        (𝓝[>] (0 : ℝ)) (𝓝 (1 / d)) := by simpa only [Function.comp_def, mul_one] using hlim
    apply hlim'.congr'
    filter_upwards [self_mem_nhdsWithin, hlog.eventually (Ioi_mem_atTop (|Real.log c| + 1))] with ε hε hl
    rw [liouvilleGraphDistance_smul μ hc hε]
    have he : ε ≠ 0 := ne_of_gt hε
    have hl0 : Real.log (ε / c)⁻¹ ≠ 0 := by
      rw [inv_div, div_eq_mul_inv, Real.log_mul (ne_of_gt hc) (inv_ne_zero he)]
      have := le_abs_self (Real.log c)
      have := neg_le_abs (Real.log c)
      linarith
    exact div_mul_div_cancel₀ hl0
  have hd := isLiouvilleGraphDimension_of_fullScale h.1 hfull
  exact ⟨hd.1, Eventually.of_forall hfinite, hd.2.2⟩

/-- Positive measure normalization leaves the graph dimension unchanged. -/
theorem isLiouvilleGraphDimension_smul_iff {μ : Measure ℂ} {z w : ℂ} {d c : ℝ}
    (hc : 0 < c) :
    IsLiouvilleGraphDimension (ENNReal.ofReal c • μ) z w d ↔
      IsLiouvilleGraphDimension μ z w d := by
  constructor
  · intro h
    have h' := h.smul (inv_pos.mpr hc)
    simpa only [smul_smul, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc)),
      inv_mul_cancel₀ (ne_of_gt hc), ENNReal.ofReal_one, one_smul] using h'
  · intro h
    exact h.smul hc


end HarmonicBalls
