import HarmonicBalls.Proofs.Sec2.GraphDimensionMeasureScaling

/-!
# Graph dimension of comparable measures

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- A cover admissible for a larger measure is admissible for a smaller one. -/
theorem IsLiouvilleGraphCover.of_measure_le {μ ν : Measure ℂ} (h : μ ≤ ν)
    {ε : ℝ} {z w : ℂ} {n : ℕ} (cover : IsLiouvilleGraphCover ν ε z w n) :
    IsLiouvilleGraphCover μ ε z w n := by
  obtain ⟨balls, hb, path, hp⟩ := cover
  refine ⟨balls, ?_, path, hp⟩
  intro i
  exact ⟨(hb i).1, (h _).trans (hb i).2⟩

/-- Graph distance is monotone in the measure, including infinite distances. -/
theorem liouvilleGraphDistance_mono_measure {μ ν : Measure ℂ} (h : μ ≤ ν)
    (ε : ℝ) (z w : ℂ) :
    liouvilleGraphDistance μ ε z w ≤ liouvilleGraphDistance ν ε z w := by
  apply sInf_le_sInf
  rintro x ⟨n, rfl, cover⟩
  exact ⟨n, rfl, cover.of_measure_le h⟩

/-- A measure between two measures with the same graph dimension has that dimension. -/
theorem isLiouvilleGraphDimension_of_measure_sandwich
    {μ ν ρ : Measure ℂ} {z w : ℂ} {d : ℝ}
    (hμ : IsLiouvilleGraphDimension μ z w d)
    (hρ : IsLiouvilleGraphDimension ρ z w d) (hμν : μ ≤ ν) (hνρ : ν ≤ ρ) :
    IsLiouvilleGraphDimension ν z w d := by
  have hlim : Tendsto (fun ε : ℝ =>
      Real.log (liouvilleGraphDistance ν ε z w).toNat / Real.log ε⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / d)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hμ.fullScale hρ.fullScale
    · filter_upwards [self_mem_nhdsWithin,
        (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).eventually
          (Ioi_mem_atTop (0 : ℝ))] with ε hε hlog
      have hmn := liouvilleGraphDistance_mono_measure hμν ε z w
      have hnr := liouvilleGraphDistance_mono_measure hνρ ε z w
      have hfρ := hρ.graphDistance_ne_top hε
      have hfν := ne_top_of_le_ne_top hfρ hnr
      have hfμ := ne_top_of_le_ne_top hfν hmn
      have hnat := ENat.toNat_le_toNat hmn hfν
      have hpos : 0 < (liouvilleGraphDistance μ ε z w).toNat := by
        have h1 := ENat.toNat_le_toNat (one_le_liouvilleGraphDistance μ ε z w) hfμ
        simp only [ENat.toNat_one] at h1
        omega
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hnat)) hlog.le
    · filter_upwards [self_mem_nhdsWithin,
        (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero).eventually
          (Ioi_mem_atTop (0 : ℝ))] with ε hε hlog
      have hnr := liouvilleGraphDistance_mono_measure hνρ ε z w
      have hfρ := hρ.graphDistance_ne_top hε
      have hfν := ne_top_of_le_ne_top hfρ hnr
      have hnat := ENat.toNat_le_toNat hnr hfρ
      have hpos : 0 < (liouvilleGraphDistance ν ε z w).toNat := by
        have h1 := ENat.toNat_le_toNat (one_le_liouvilleGraphDistance ν ε z w) hfν
        simp only [ENat.toNat_one] at h1
        omega
      exact div_le_div_of_nonneg_right
        (Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hnat)) hlog.le
  exact isLiouvilleGraphDimension_of_fullScale hμ.1 hlim

/-- Constant two-sided measure bounds preserve the graph-dimension exponent. -/
theorem isLiouvilleGraphDimension_iff_of_comparable
    {μ ν : Measure ℂ} {z w : ℂ} {d c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlower : ENNReal.ofReal c • μ ≤ ν) (hupper : ν ≤ ENNReal.ofReal C • μ) :
    IsLiouvilleGraphDimension ν z w d ↔ IsLiouvilleGraphDimension μ z w d := by
  have hinvC : ENNReal.ofReal C⁻¹ • ν ≤ μ := by
    have h := smul_le_smul_left (ENNReal.ofReal C⁻¹) hupper
    simpa only [smul_smul, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hC)),
      inv_mul_cancel₀ (ne_of_gt hC), ENNReal.ofReal_one, one_smul] using h
  have hinvc : μ ≤ ENNReal.ofReal c⁻¹ • ν := by
    have h := smul_le_smul_left (ENNReal.ofReal c⁻¹) hlower
    simpa only [smul_smul, ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr hc)),
      inv_mul_cancel₀ (ne_of_gt hc), ENNReal.ofReal_one, one_smul] using h
  constructor
  · intro h
    exact isLiouvilleGraphDimension_of_measure_sandwich (h.smul (inv_pos.mpr hC))
      (h.smul (inv_pos.mpr hc)) hinvC hinvc
  · intro h
    exact isLiouvilleGraphDimension_of_measure_sandwich (h.smul hc) (h.smul hC)
      hlower hupper


end HarmonicBalls
