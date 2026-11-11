import HarmonicBalls.Steps.Sec11.WeylHomeomorph
import HarmonicBalls.Steps.Sec11.WeylScalingOrder

/-! # Dilation of a logarithmically singular Weyl weight

The pointwise logarithm identity holds away from the origin. The pathwise
zero-occupation condition is kept explicit here and is not a literature input.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter
open scoped ENNReal

/-- Weyl scaling depends only on the weight almost everywhere along each
length-parametrized path. No measurability of the weight is required. -/
theorem weylScaling_congr_path_ae (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f g : ℂ → ℝ)
    (hfg : ∀ T p, IsLengthParametrized D p T →
      ∀ᵐ t ∂(volume.restrict (Icc 0 T)), f (p t) = g (p t)) (u v : ℂ) :
    weylScaling D ξ f u v = weylScaling D ξ g u v := by
  unfold weylScaling
  apply iInf_congr; intro T
  apply iInf_congr; intro p
  apply iInf_congr; intro hp
  apply iInf_congr; intro hu
  apply iInf_congr; intro hv
  apply lintegral_congr_ae
  filter_upwards [hfg T p hp] with t ht
  rw [ht]

/-- Dilation of a logarithmically singular Weyl scaling, provided that every
admissible path spends zero Lebesgue time at the origin. -/
theorem weylScaling_log_comp_real_smul (D : ℂ → ℂ → ℝ) (ξ α : ℝ)
    {k : ℝ} (hk : 0 < k)
    (hzero : ∀ T p, IsLengthParametrized (fun x y => D (k • x) (k • y)) p T →
      ∀ᵐ t ∂(volume.restrict (Icc 0 T)), p t ≠ 0) (u v : ℂ) :
    weylScaling (fun x y => D (k • x) (k • y)) ξ
        (fun x => -α * Real.log ‖x‖) u v =
      ENNReal.ofReal (Real.exp (ξ * (α * Real.log k))) *
        weylScaling D ξ (fun x => -α * Real.log ‖x‖) (k • u) (k • v) := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  let f : ℂ → ℝ := fun x => -α * Real.log ‖x‖
  have hweight : ∀ z : ℂ, z ≠ 0 → f z = f (e z) + α * Real.log k := by
    intro z hz
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    change -α * Real.log ‖z‖ = -α * Real.log ‖k • z‖ + α * Real.log k
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk, Real.log_mul hk.ne' hn]
    ring
  change weylScaling (fun x y => D (e x) (e y)) ξ f u v =
    ENNReal.ofReal (Real.exp (ξ * (α * Real.log k))) *
      weylScaling D ξ f (e u) (e v)
  calc
    weylScaling (fun x y => D (e x) (e y)) ξ f u v =
        weylScaling (fun x y => D (e x) (e y)) ξ
          (fun z => f (e z) + α * Real.log k) u v := by
      apply weylScaling_congr_path_ae
      intro T p hp
      filter_upwards [hzero T p hp] with t ht
      exact hweight (p t) ht
    _ = ENNReal.ofReal (Real.exp (ξ * (α * Real.log k))) *
        weylScaling (fun x y => D (e x) (e y)) ξ (f ∘ e) u v :=
      weylScaling_add_const _ _ _ _ _ _
    _ = _ := by rw [weylScaling_comp_homeomorph]


/-- The zero-occupation condition may be checked for paths in the original
metric before pulling it back by dilation. -/
theorem weylScaling_log_comp_real_smul_of_base_zero_occupation
    (D : ℂ → ℂ → ℝ) (ξ α : ℝ) {k : ℝ} (hk : 0 < k)
    (hzero : ∀ T p, IsLengthParametrized D p T →
      ∀ᵐ t ∂(volume.restrict (Icc 0 T)), p t ≠ 0) (u v : ℂ) :
    weylScaling (fun x y => D (k • x) (k • y)) ξ
        (fun x => -α * Real.log ‖x‖) u v =
      ENNReal.ofReal (Real.exp (ξ * (α * Real.log k))) *
        weylScaling D ξ (fun x => -α * Real.log ‖x‖) (k • u) (k • v) := by
  apply weylScaling_log_comp_real_smul D ξ α hk
  intro T p hp
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have hp' : IsLengthParametrized D (e ∘ p) T := by
    change IsLengthParametrized (fun x y => D (e x) (e y)) p T at hp
    have h := hp.comp_homeomorph_symm e.symm
    simpa only [e.symm_symm, e.apply_symm_apply] using h
  filter_upwards [hzero T (e ∘ p) hp'] with t ht
  change k • p t ≠ 0 at ht
  intro hpt
  apply ht
  rw [hpt, smul_zero]


end HarmonicBalls
