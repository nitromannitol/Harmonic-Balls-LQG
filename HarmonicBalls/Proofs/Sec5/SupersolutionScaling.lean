import HarmonicBalls.Proofs.Sec5.LaplacianScaling
import HarmonicBalls.Proofs.Sec5.GreenScaling
import HarmonicBalls.Defs.Obstacle
import HarmonicBalls.Steps.Sec5.ScaleInvariance

/-! # Scaling the obstacle problem -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- Dilation and positive multiplication carry supersolutions to
supersolutions for the corresponding pulled-back measure and time. -/
theorem supersolutions_comp_real_smul {μ : Measure ℂ} {R k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) {w : ℂ → ℝ}
    (hw : w ∈ supersolutions μ (k * R) (k • z) t) :
    (fun x => c * w (k • x)) ∈
      supersolutions (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) R z (c * t) := by
  have hball (x : ℂ) : k • x ∈ ball (0 : ℂ) (k * R) ↔ x ∈ ball (0 : ℂ) R := by
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    exact mul_lt_mul_iff_right₀ hk
  have hclosed (x : ℂ) : k • x ∈ closedBall (0 : ℂ) (k * R) ↔
      x ∈ closedBall (0 : ℂ) R := by
    simp only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    exact mul_le_mul_iff_right₀ hk
  have hset : (fun x : ℂ => k • x) ⁻¹' ball (0 : ℂ) (k * R) = ball 0 R := by
    ext x
    exact hball x
  refine ⟨?_, ?_, ?_⟩
  · exact continuousOn_const.mul (hw.1.comp (continuous_const_smul k).continuousOn
      (fun x hx => (hclosed x).2 hx))
  · have h := (hw.2.1.comp_real_smul hk).const_mul hc
    rwa [hset] at h
  · intro x hx hxz
    have hxz' : k • x ≠ k • z := by
      intro heq
      apply hxz
      have h := congrArg (fun y : ℂ => k⁻¹ • y) heq
      simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h
    have h := mul_le_mul_of_nonneg_left (hw.2.2 (k • x) ((hclosed x).2 hx) hxz') hc.le
    rw [greenFunction_ball_smul hk] at h
    convert h using 1; ring

/-- The normalized pullback and its inverse return the original measure. -/
theorem inverse_scaled_measure {μ : Measure ℂ} {k c : ℝ} (hk : 0 < k) (hc : 0 < c) :
    ENNReal.ofReal c⁻¹ • Measure.map (fun x : ℂ => k • x)
      (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) = μ := by
  rw [Measure.map_smul _ (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  have hf : (fun x : ℂ => k • x) ∘ (fun x : ℂ => k⁻¹ • x) = id := by
    funext x
    simp only [Function.comp_apply, smul_smul, mul_inv_cancel₀ hk.ne', one_smul, id_eq]
  rw [hf, Measure.map_id, smul_smul, ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le),
    inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one, one_smul]

/-- Every supersolution of the scaled problem comes from the original
problem by dilation and positive multiplication. -/
theorem supersolutions_comp_real_smul_inv {μ : Measure ℂ} {R k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) {v : ℂ → ℝ}
    (hv : v ∈ supersolutions (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ)
      R z (c * t)) :
    (fun x => c⁻¹ * v (k⁻¹ • x)) ∈ supersolutions μ (k * R) (k • z) t := by
  have hv' : v ∈ supersolutions (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ)
      (k⁻¹ * (k * R)) (k⁻¹ • (k • z)) (c * t) := by
    simpa only [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, smul_smul, one_smul] using hv
  have h := supersolutions_comp_real_smul (k := k⁻¹) (c := c⁻¹)
    (R := k * R) (z := k • z) (t := c * t)
    (inv_pos.mpr hk) (inv_pos.mpr hc) hv'
  simpa only [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul, smul_smul, one_smul,
    inv_mul_cancel₀ hc.ne', inv_inv, inverse_scaled_measure hk hc] using h

/-- Away from the pole, the least supersolution scales with the obstacle. -/
theorem leastSupersolution_comp_real_smul {μ : Measure ℂ} {R k c t : ℝ} {z x : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    leastSupersolution (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ)
      R z (c * t) x = c * leastSupersolution μ (k * R) (k • z) t (k • x) := by
  have hx' : k • x ∈ closedBall (0 : ℂ) (k * R) := by
    simp only [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hk] at hx ⊢
    exact mul_le_mul_of_nonneg_left hx hk.le
  have hxz' : k • x ≠ k • z := by
    intro heq
    apply hxz
    have h := congrArg (fun y : ℂ => k⁻¹ • y) heq
    simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h
  let S := (fun w : ℂ → ℝ => w (k • x)) '' supersolutions μ (k * R) (k • z) t
  have heq : (fun v : ℂ → ℝ => v x) ''
      supersolutions (ENNReal.ofReal c • Measure.map (fun y : ℂ => k⁻¹ • y) μ) R z (c * t) =
      (fun a : ℝ => c * a) '' S := by
    ext a
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(fun y => c⁻¹ * v (k⁻¹ • y)) (k • x),
        ⟨_, supersolutions_comp_real_smul_inv hk hc hv, rfl⟩, ?_⟩
      simp only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul, ← mul_assoc,
        mul_inv_cancel₀ hc.ne', one_mul]
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨fun y => c * w (k • y), supersolutions_comp_real_smul hk hc hw, rfl⟩
  have hnonempty : S.Nonempty := (supersolutions_nonempty μ (k * R) (k • z) ht).image _
  have hbdd : BddBelow S := bddBelow_supersolutions hx' hxz'
  have hiso := (OrderIso.mulLeft₀ c hc).map_csInf' hnonempty hbdd
  change c * sInf S = sInf ((fun a : ℝ => c * a) '' S) at hiso
  change sInf _ = c * sInf S
  rw [heq]
  exact hiso.symm

/-- The non-coincidence set is the inverse image of the original cluster. -/
theorem cluster_comp_real_smul {μ : Measure ℂ} {R k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) :
    cluster (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) R z (c * t) =
      (fun x : ℂ => k • x) ⁻¹' cluster μ (k * R) (k • z) t := by
  ext x
  have hball : k • x ∈ ball (0 : ℂ) (k * R) ↔ x ∈ ball (0 : ℂ) R := by
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    exact mul_lt_mul_iff_right₀ hk
  have hpole : k • x = k • z ↔ x = z := by
    constructor
    · intro heq
      have h := congrArg (fun y : ℂ => k⁻¹ • y) heq
      simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using h
    · rintro rfl
      rfl
  simp only [cluster, mem_ofPred_eq, mem_preimage, hball, hpole]
  by_cases hx : x ∈ ball (0 : ℂ) R
  · by_cases hxz : x = z
    · simp [hxz]
    · simp only [hx, hxz, false_or, true_and]
      rw [leastSupersolution_comp_real_smul hk hc ht (ball_subset_closedBall hx) hxz,
        greenFunction_ball_smul hk]
      have hobs : -(c * t) * greenFunction (ball 0 R) z x =
          c * (-t * greenFunction (ball 0 R) z x) := by ring
      rw [hobs]
      exact mul_lt_mul_iff_right₀ hc
  · simp [hx]

/-- The scaled cluster is the inverse dilation of the original cluster,
with the time normalized by the same factor as the measure. -/
theorem cluster_scaled_measure {μ : Measure ℂ} {R k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) :
    cluster (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) R z t =
      k⁻¹ • cluster μ (k * R) (k • z) (c⁻¹ * t) := by
  have h := cluster_comp_real_smul (μ := μ) (R := R) (z := z) (k := k)
    (c := c) (t := c⁻¹ * t) hk hc (mul_nonneg (inv_nonneg.mpr hc.le) ht)
  have heq : (fun x : ℂ => k • x) ⁻¹' cluster μ (k * R) (k • z) (c⁻¹ * t) =
      k⁻¹ • cluster μ (k * R) (k • z) (c⁻¹ * t) := by
    ext x
    simp only [mem_preimage, Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hk.ne'), inv_inv]
  rw [heq] at h
  simpa only [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] using h

/-- The pathwise scale change of Lemma 5.7 follows for every measure;
no probabilistic assumptions are needed for this step. -/
theorem clusterPathwiseScaleStep_proved : ClusterPathwiseScaleStep := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ k hk
  filter_upwards [] with ω z hz t ht
  let a := Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0))
  have ha : 0 < a := Real.exp_pos _
  have h := cluster_scaled_measure (μ := μ ω) (R := 1) (z := z) (k := k)
    (c := a⁻¹) (t := t) hk (inv_pos.mpr ha) ht.le
  simpa only [normalizedPullbackMeasure, ← ENNReal.ofReal_inv_of_pos ha,
    inv_inv, mul_one, a] using h

end HarmonicBalls
