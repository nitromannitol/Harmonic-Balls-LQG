import HarmonicBalls.Proofs.Sec6.LaplacianTranslation
import HarmonicBalls.Proofs.Sec9.AuxiliaryPotential

/-! # Translation of disc-potential regularity

Local finiteness and volume growth can be translated from an ambient disc to
a smaller disc with arbitrary centre.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Laplacian
open scoped Topology

/-- The inverse image of a disc under translation is the translated disc. -/
theorem preimage_ball_sub_right (c x : ℂ) (r : ℝ) :
    (fun y : ℂ => y - c) ⁻¹' ball x r = ball (x + c) r := by
  ext y
  simp only [mem_preimage, mem_ball, dist_eq_norm]
  ring

/-- Translating a locally finite planar measure preserves local finiteness. -/
theorem isLocallyFiniteMeasure_map_sub_right {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) (c : ℂ) :
    IsLocallyFiniteMeasure (μ.map (fun z => z - c)) := by
  let : IsLocallyFiniteMeasure μ := hμ
  refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x (by norm_num), ?_⟩⟩
  rw [Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_right]
  exact measure_ball_lt_top

/-- Volume growth on an ambient disc transfers to a translated subdisc. -/
theorem volumeGrowth_map_sub_right {μ : Measure ℂ} {R r βm βp : ℝ} {c : ℂ}
    (hV : VolumeGrowth μ R βm βp) (hsub : ball c r ⊆ ball 0 R) :
    VolumeGrowth (μ.map (fun z => z - c)) r βm βp := by
  obtain ⟨hβm, hβp, r₀, hr₀, hgrowth⟩ := hV
  refine ⟨hβm, hβp, r₀, hr₀, fun s hs hs₀ x hx => ?_⟩
  have hx' : x + c ∈ ball c r := by
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
  rw [Measure.map_apply (by fun_prop) measurableSet_ball, preimage_ball_sub_right]
  exact hgrowth s hs hs₀ (x + c) (hsub hx')

/-- Restricted Green potentials on arbitrary discs are continuous up to the
boundary and have the expected distributional Laplacian. -/
theorem restricted_greenPotential_center_regular {μ : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) {R r βm βp : ℝ} {c : ℂ}
    (hr : 0 < r) (hV : VolumeGrowth μ R βm βp)
    (hsub : ball c r ⊆ ball 0 R) {A : Set ℂ} (hA : A ⊆ ball c r) :
    ContinuousOn (fun x => ∫ y in A, greenFunction (ball c r) x y ∂μ) (closedBall c r) ∧
    HasLaplacian (fun x => ∫ y in A, greenFunction (ball c r) x y ∂μ)
      0 (μ.restrict A) (ball c r) := by
  let ν := μ.map (fun z : ℂ => z - c)
  let A' := (fun z : ℂ => z + c) ⁻¹' A
  have hA' : A' ⊆ ball (0 : ℂ) r := by
    intro x hx
    have h := hA hx
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using h
  obtain ⟨hc, hΔ⟩ := restricted_greenPotential_regular
    (isLocallyFiniteMeasure_map_sub_right hμ c) hr (volumeGrowth_map_sub_right hV hsub) hA'
  have hrest : ν.restrict A' = (μ.restrict A).map (fun z : ℂ => z - c) := by
    let e : ℂ ≃ᵐ ℂ := (Homeomorph.addRight (-c)).toMeasurableEquiv
    have h := e.restrict_map μ A'
    have hpre : (fun z : ℂ => z - c) ⁻¹' A' = A := by
      ext z
      change (z - c) + c ∈ A ↔ z ∈ A
      rw [sub_add_cancel]
    change ν.restrict A' = (μ.restrict ((fun z : ℂ => z - c) ⁻¹' A')).map
      (fun z : ℂ => z - c) at h
    rw [hpre] at h
    exact h
  have hball : (fun z : ℂ => z + c) '' ball 0 r = ball c r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
    · intro hz
      refine ⟨z - c, ?_, sub_add_cancel z c⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
  have hq : (fun x => ∫ y in A, greenFunction (ball c r) x y ∂μ) =
      fun x => ∫ y in A', greenFunction (ball 0 r) (x - c) y ∂ν := by
    funext x
    have h := greenPotential_translate (O := ball 0 r) isOpen_ball (μ.restrict A) c (x - c)
    rw [hball, sub_add_cancel] at h
    rw [← hrest] at h
    exact h
  rw [hq]
  refine ⟨?_, ?_⟩
  · apply hc.comp (continuous_id.sub continuous_const).continuousOn
    intro x hx
    change x - c ∈ closedBall (0 : ℂ) r
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hx
  · have h := hasLaplacian_comp_add_right hΔ (-c)
    have hmap : Measure.map (fun z : ℂ => z - (-c)) (ν.restrict A') = μ.restrict A := by
      rw [hrest, Measure.map_map (by fun_prop) (by fun_prop)]
      simp only [Function.comp_def, sub_neg_eq_add, sub_add_cancel]
      exact Measure.map_id
    have hdomain : (fun z : ℂ => z + -c) ⁻¹' ball 0 r = ball c r := by
      simpa only [sub_eq_add_neg, zero_add] using preimage_ball_sub_right c 0 r
    change HasLaplacian (fun x => ∫ y in A', greenFunction (ball 0 r) (x + -c) y ∂ν)
      (Measure.map (fun z : ℂ => z - (-c)) 0)
      (Measure.map (fun z : ℂ => z - (-c)) (ν.restrict A')) _ at h
    rw [Measure.map_zero, hmap, hdomain] at h
    simpa only [sub_eq_add_neg] using h

end HarmonicBalls.Section6
