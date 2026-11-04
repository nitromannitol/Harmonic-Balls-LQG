import MarkovProcess.Trajectory.Equivariance
import HarmonicBalls.Proofs.Sec8.GoodAnnulusScaling
import HarmonicBalls.Proofs.Brownian.PlanarBrownianMotion
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller

/-! # Exit times under path rescaling -/

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HarmonicBalls

open MarkovProcess

/-- The exit time is the infimum of the times at which the path is outside. -/
theorem exitTime_eq_iInf {E : Type*} [TopologicalSpace E] (U : Set E)
    (ω : ContinuousPath E) :
    ContinuousPath.exitTime U ω = ⨅ t : ℝ≥0, ⨅ (_ : ω t ∉ U), (t : ℝ≥0∞) := by
  unfold ContinuousPath.exitTime
  apply le_antisymm
  · refine le_iInf fun t => le_iInf fun ht => ?_
    exact sInf_le ⟨t, rfl, ht⟩
  · apply le_sInf
    rintro _ ⟨t, rfl, ht⟩
    exact iInf_le_of_le t (iInf_le _ ht)

/-- Exit times transform by the inverse time factor under continuous-path
rescaling, for arbitrary sets and without exit-time measurability assumptions. -/
theorem exitTime_rescale_mul {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (e : E ≃ₜ F) (c : ℝ≥0) (hc : 0 < c) (U : Set F) (ω : ContinuousPath E) :
    (c : ℝ≥0∞) * ContinuousPath.exitTime U (ContinuousPath.rescale e c ω) =
      ContinuousPath.exitTime (e ⁻¹' U) ω := by
  rw [exitTime_eq_iInf, exitTime_eq_iInf]
  rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hc.ne') ENNReal.coe_ne_top]
  simp_rw [ENNReal.mul_iInf_of_ne (by exact_mod_cast hc.ne') ENNReal.coe_ne_top]
  have hs : Function.Surjective (fun t : ℝ≥0 => c * t) := by
    intro t
    exact ⟨c⁻¹ * t, by simp [hc.ne']⟩
  simpa only [ContinuousPath.rescale_apply, mem_preimage, ← ENNReal.coe_mul] using
    (hs.iInf_comp (fun t : ℝ≥0 => ⨅ (_ : ω t ∉ e ⁻¹' U), (t : ℝ≥0∞)))

/-- Positive time rescaling preserves the order of two exit times. -/
theorem rescale_preimage_exitTime_le {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (e : E ≃ₜ F) (c : ℝ≥0) (hc : 0 < c) (U V : Set F) :
    (ContinuousPath.rescale e c) ⁻¹'
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime V ω} =
    {ω | ContinuousPath.exitTime (e ⁻¹' U) ω ≤ ContinuousPath.exitTime (e ⁻¹' V) ω} := by
  ext ω
  simp only [mem_preimage, mem_ofPred_eq]
  rw [← exitTime_rescale_mul e c hc U ω, ← exitTime_rescale_mul e c hc V ω,
    ENNReal.mul_le_mul_iff_right (by exact_mod_cast hc.ne') ENNReal.coe_ne_top]

/-- Space-time rescaling is a homeomorphism of continuous-path spaces when the
time factor is positive. -/
noncomputable def continuousPathRescaleHomeomorph {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (e : E ≃ₜ F) (c : ℝ≥0) (hc : 0 < c) : ContinuousPath E ≃ₜ ContinuousPath F where
  toFun := ContinuousPath.rescale e c
  invFun := ContinuousPath.rescale e.symm c⁻¹
  left_inv := by
    intro ω
    rw [ContinuousPath.rescale_rescale]
    simp [hc.ne']
  right_inv := by
    intro ω
    rw [ContinuousPath.rescale_rescale]
    simp [hc.ne']
  continuous_toFun := ContinuousPath.continuous_rescale e c
  continuous_invFun := ContinuousPath.continuous_rescale e.symm c⁻¹

/-- The image law of a rescaled path transports the outer measure of an
exit-time comparison, including when the event is not known measurable. -/
theorem measure_exitTime_le_map_rescale (μ : Measure (ContinuousPath ℂ))
    (e : ℂ ≃ₜ ℂ) (c : ℝ≥0) (hc : 0 < c) (U V : Set ℂ) :
    (μ.map (ContinuousPath.rescale e c))
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime V ω} =
    μ {ω | ContinuousPath.exitTime (e ⁻¹' U) ω ≤ ContinuousPath.exitTime (e ⁻¹' V) ω} := by
  change (μ.map (continuousPathRescaleHomeomorph e c hc)) _ = _
  rw [(continuousPathRescaleHomeomorph e c hc).measurableEmbedding.map_apply]
  exact congrArg μ (rescale_preimage_exitTime_le e c hc U V)

open MarkovProcess in
/-- A Brownian path scaling identity implies transport of exit-event outer
probabilities for all sets. -/
theorem planarBrownian_exit_probability_of_path_rescaling {k : ℝ} (hk : 0 < k)
    (c : ℝ≥0) (hc : 0 < c)
    (hpath : ∀ u : ℂ, planarBrownianMotion (k • u) =
      (planarBrownianMotion u).map
        (ContinuousPath.rescale (Homeomorph.smulOfNeZero k hk.ne') c))
    (r : ℝ) (z : ℂ) (Y : Set ℂ) (u : ℂ) :
    planarBrownianMotion u
      {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
        ContinuousPath.exitTime Y p} =
    planarBrownianMotion (k • u)
      {p | ContinuousPath.exitTime (annulus (k • z) (3 * (k * r)) (5 * (k * r))) p ≤
        ContinuousPath.exitTime ((fun x : ℂ => k⁻¹ • x) ⁻¹' Y) p} := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have hA : (fun x : ℂ => k⁻¹ • x) ⁻¹' annulus z (3 * r) (5 * r) =
      annulus (k • z) (3 * (k * r)) (5 * (k * r)) := by
    rw [preimage_inv_smul_annulus hk]
    congr 1 <;> ring
  have hpre (S : Set ℂ) : e ⁻¹' ((fun x : ℂ => k⁻¹ • x) ⁻¹' S) = S := by
    ext x
    simp only [mem_preimage, e, Homeomorph.smulOfNeZero_apply, smul_smul,
      inv_mul_cancel₀ hk.ne', one_smul]
  rw [← hA, hpath u, measure_exitTime_le_map_rescale _ e c hc, hpre, hpre]

/-- Conjugacy of the planar heat semigroup implies the corresponding
space-time scaling law for planar Brownian paths. -/
theorem planarBrownianMotion_map_rescale_of_heat_conjugacy (e : ℂ ≃ₜ ℂ)
    (c : ℝ≥0) (hc : 0 < c)
    (h : SubMarkovKernelSemigroup.IsRescaledConjugate planarHeatSemigroup planarHeatSemigroup e c)
    (u : ℂ) :
    planarBrownianMotion (e u) =
      (planarBrownianMotion u).map (ContinuousPath.rescale e c) := by
  rw [planarBrownianMotion_eq_continuousProcess]
  have hh := SubMarkovKernelSemigroup.IsConservative.continuousProcess_apply_rescale
    planarHeatSemigroup isConservative_planarHeatSemigroup
    planarHeatSemigroup isConservative_planarHeatSemigroup
    isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup
    kolmogorovRegular_planarHeatSemigroup hc h (e u)
  simpa only [Homeomorph.symm_apply_apply] using hh

/-- The planar heat kernel is invariant under Brownian space-time dilation. -/
theorem planarHeatSemigroup_dilation_conjugate {k : ℝ} (hk : 0 < k) :
    SubMarkovKernelSemigroup.IsRescaledConjugate planarHeatSemigroup planarHeatSemigroup
      (Homeomorph.smulOfNeZero k hk.ne') (⟨k, hk.le⟩⁻¹ ^ 2 : ℝ≥0) := by
  intro t z
  rw [planarHeatSemigroup_apply, planarHeatSemigroup_apply,
    planarGaussian_eq_map_add_sqrt_mul, planarGaussian_eq_map_add_sqrt_mul,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext w
  have hs : k * Real.sqrt (((⟨k, hk.le⟩⁻¹ ^ 2 * t : ℝ≥0) : ℝ)) = Real.sqrt t := by
    change k * Real.sqrt (k⁻¹ ^ 2 * (t : ℝ)) = Real.sqrt t
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
      abs_of_pos (inv_pos.mpr hk)]
    field_simp
  simp only [Function.comp_apply, Homeomorph.smulOfNeZero_apply,
    Homeomorph.smulOfNeZero_symm_apply, Complex.real_smul]
  have hh := congrArg (fun x : ℝ => (x : ℂ)) hs
  rw [Complex.ofReal_mul] at hh
  calc
    z + (Real.sqrt ↑t : ℂ) * w = z + ((k : ℂ) *
        (Real.sqrt (((⟨k, hk.le⟩⁻¹ ^ 2 * t : ℝ≥0) : ℝ)) : ℂ)) * w := by rw [hh]
    _ = (k : ℂ) * ((k⁻¹ : ℝ) • z +
        (Real.sqrt (((⟨k, hk.le⟩⁻¹ ^ 2 * t : ℝ≥0) : ℝ)) : ℂ) * w) := by
      simp only [Complex.real_smul, Complex.ofReal_inv]
      have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      field_simp

/-- Brownian space-time scaling of planar Brownian motion. -/
theorem planarBrownianMotion_map_dilation {k : ℝ} (hk : 0 < k) (u : ℂ) :
    planarBrownianMotion (k • u) = (planarBrownianMotion u).map
      (ContinuousPath.rescale (Homeomorph.smulOfNeZero k hk.ne')
        (⟨k, hk.le⟩⁻¹ ^ 2 : ℝ≥0)) := by
  have hkn : (0 : ℝ≥0) < ⟨k, hk.le⟩ := by exact_mod_cast hk
  have hc : (0 : ℝ≥0) < ⟨k, hk.le⟩⁻¹ ^ 2 := pow_pos (inv_pos.mpr hkn) 2
  simpa only [Homeomorph.smulOfNeZero_apply] using
    planarBrownianMotion_map_rescale_of_heat_conjugacy (Homeomorph.smulOfNeZero k hk.ne')
      _ hc (planarHeatSemigroup_dilation_conjugate hk) u

open MarkovProcess in
/-- Dilation preserves planar Brownian exit-event outer probabilities. -/
theorem planarBrownian_exit_probability_dilation {k : ℝ} (hk : 0 < k)
    (r : ℝ) (z : ℂ) (Y : Set ℂ) (u : ℂ) :
    planarBrownianMotion u
      {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
        ContinuousPath.exitTime Y p} =
    planarBrownianMotion (k • u)
      {p | ContinuousPath.exitTime (annulus (k • z) (3 * (k * r)) (5 * (k * r))) p ≤
        ContinuousPath.exitTime ((fun x : ℂ => k⁻¹ • x) ⁻¹' Y) p} := by
  have hkn : (0 : ℝ≥0) < ⟨k, hk.le⟩ := by exact_mod_cast hk
  have hc : (0 : ℝ≥0) < ⟨k, hk.le⟩⁻¹ ^ 2 := pow_pos (inv_pos.mpr hkn) 2
  exact planarBrownian_exit_probability_of_path_rescaling hk _ hc
    (planarBrownianMotion_map_dilation hk) r z Y u

/-- The good-annulus condition is invariant under positive spatial dilation. -/
theorem isGoodAnnulus_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (r : ℝ) (z : ℂ) (a b : ℝ) :
    IsGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) r z a b ↔
      IsGoodAnnulus μ (k * r) (k • z) a b := by
  apply isGoodAnnulus_map_inv_smul_of_exit_probability μ hk r z a b
  intro Y _ u
  exact planarBrownian_exit_probability_dilation hk r z Y u

/-- The very-good-annulus event at the origin is invariant under simultaneous
positive dilation of the measure and the scale. -/
theorem isVeryGoodAnnulus_map_inv_smul (μ : Measure ℂ) {k : ℝ} (hk : 0 < k)
    (β ρ : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus (μ.map (fun x : ℂ => k⁻¹ • x)) β ρ 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ↔
      IsVeryGoodAnnulus μ β (k * ρ) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ := by
  apply isVeryGoodAnnulus_map_inv_smul_of_good_transport μ hk
  intro r z
  exact isGoodAnnulus_map_inv_smul μ hk r z a b

universe u
open Filter ProbabilityTheory

open Classical in
/-- Joint very-good and comparison indicators are stationary under the
staged affine and LQG coordinate-change inputs, once the very-good events
are measurable. -/
theorem identDistrib_lqg_veryGoodComparable_sequence_of_measurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hmeas : ∀ n, MeasurableSet {ν : Measure ℂ |
      IsVeryGoodAnnulus ν β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃}) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  apply identDistrib_lqg_veryGoodComparable_sequence_of_good_transport hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m hmeas
  filter_upwards [] with ω r z
  exact isGoodAnnulus_map_inv_smul (μ ω) (dyadicScale_pos 1) r z a b

end HarmonicBalls
