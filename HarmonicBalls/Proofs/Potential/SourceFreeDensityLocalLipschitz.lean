import HarmonicBalls.Proofs.Potential.SourceFreeUniformDensityConvergence
import HarmonicBalls.Proofs.Potential.DiscPoisson

/-! # Local Lipschitz bounds for source-free Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls
open Complex Metric Real Set MeasureTheory InnerProductSpace
open scoped Topology

private theorem poissonKernel_center_difference {x y ζ : ℂ} {r : ℝ}
    (hr : 0 < r) (hy : dist y x < r / 2) (hζ : ζ ∈ sphere x r) :
    |poissonKernel x y ζ - 1| ≤ (4 / r) * dist y x := by
  have hζx : ‖ζ - x‖ = r := by simpa [dist_eq_norm] using hζ
  have hyx : ‖y - x‖ < r / 2 := by simpa [dist_eq_norm] using hy
  have hlow : r / 2 ≤ ‖ζ - y‖ := by
    have h := norm_sub_norm_le (ζ - x) (y - x)
    have he : ζ - x - (y - x) = ζ - y := by ring
    rw [he, hζx] at h
    linarith
  have hne : ζ - x - (y - x) ≠ 0 := by
    have he : ζ - x - (y - x) = ζ - y := by ring
    rw [he]
    exact norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hlow)
  have heq : poissonKernel x y ζ - 1 =
      (((2 : ℂ) * (y - x)) / ((ζ - x) - (y - x))).re := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    simp only [Function.comp_apply, herglotzRieszKernel_def]
    change (((ζ - x + (y - x)) / (ζ - x - (y - x))).re - (1 : ℂ).re) = _
    rw [← Complex.sub_re]
    congr 1
    field_simp [hne]
    ring
  rw [heq]
  calc
    |(((2 : ℂ) * (y - x)) / ((ζ - x) - (y - x))).re| ≤
        ‖((2 : ℂ) * (y - x)) / ((ζ - x) - (y - x))‖ := Complex.abs_re_le_norm _
    _ = 2 * ‖y - x‖ / ‖ζ - y‖ := by
      rw [norm_div, norm_mul, Complex.norm_ofNat]
      congr 1
      ring
    _ ≤ (4 / r) * dist y x := by
      rw [dist_eq_norm]
      apply (div_le_iff₀ (lt_of_lt_of_le (by positivity) hlow)).2
      have : 0 ≤ ‖y - x‖ := norm_nonneg _
      have hr' : 0 < r := hr
      field_simp
      nlinarith


private theorem harmonic_difference_le {f : ℂ → ℝ} {x y : ℂ} {r M : ℝ}
    (hr : 0 < r) (hh : HarmonicOnNhd f (closedBall x r))
    (hM : ∀ z ∈ sphere x r, |f z| ≤ M)
    (hy : dist y x < r / 2) :
    |f y - f x| ≤ ((4 / r) * M) * dist y x := by
  have hyball : y ∈ ball x r := by rw [mem_ball]; linarith
  have hxball : x ∈ ball x r := mem_ball_self hr
  have hcont : ContinuousOn f (sphere x |r|) := by
    rw [abs_of_pos hr]
    exact hh.continuousOn.mono sphere_subset_closedBall
  have hci : CircleIntegrable f x r := hcont.circleIntegrable'
  have hki := CircleIntegrable.poissonKernel_smul hci hyball
  have hkj := CircleIntegrable.poissonKernel_smul hci hxball
  have heq : f y - f x = Real.circleAverage
      (fun ζ => (poissonKernel x y ζ - 1) * f ζ) x r := by
    rw [← hh.circleAverage_poissonKernel_smul hyball,
      ← hh.circleAverage_poissonKernel_smul hxball,
      ← circleAverage_fun_sub hki hkj]
    apply circleAverage_congr_sphere
    intro ζ hζ
    rw [abs_of_pos hr] at hζ
    simp only [smul_eq_mul, Pi.mul_apply, poissonKernel_self hζ hr.ne']
    ring
  have hint : CircleIntegrable (fun ζ => (poissonKernel x y ζ - 1) * f ζ) x r := by
    apply ((continuousOn_poissonKernel hyball).sub continuousOn_const).mul hcont |>.circleIntegrable'
  have hc : CircleIntegrable (fun _ : ℂ => (4 / r * dist y x) * M) x r :=
    continuousOn_const.circleIntegrable'
  rw [heq]
  calc
    |Real.circleAverage (fun ζ => (poissonKernel x y ζ - 1) * f ζ) x r| ≤
        Real.circleAverage |fun ζ => (poissonKernel x y ζ - 1) * f ζ| x r :=
          abs_circleAverage_le_circleAverage_abs
    _ ≤ Real.circleAverage (fun _ : ℂ => (4 / r * dist y x) * M) x r := by
      apply circleAverage_mono hint.abs hc
      intro ζ hζ
      rw [abs_of_pos hr] at hζ
      change |(poissonKernel x y ζ - 1) * f ζ| ≤ _
      rw [abs_mul]
      exact mul_le_mul (poissonKernel_center_difference hr hy hζ) (hM ζ hζ)
        (abs_nonneg _) (by positivity)
    _ = ((4 / r) * M) * dist y x := by rw [circleAverage_const]; ring


/-- On a uniform geometric scale around a compact set, source-free signed-density
Green potentials are Lipschitz with constant proportional to the density's L¹ norm.
The Green source is the first kernel argument. -/
theorem sigmaFinite_source_free_density_green_local_lipschitz
    {V U K : Set ℂ} {ν : Measure ℂ} [SigmaFinite ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hν : ∀ᵐ y ∂ν, y ∈ V)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hUV : U ⊆ V) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∀ (f : ℂ → ℝ), Measurable f → Integrable f ν →
      (∀ᵐ y ∂ν, y ∈ U → f y = 0) → ∀ x ∈ K, ∀ y : ℂ, dist y x < δ →
      |(∫ z, f z * greenFunction V z y ∂ν) - (∫ z, f z * greenFunction V z x ∂ν)| ≤
        (C * ∫ z, |f z| ∂ν) * dist y x := by
  obtain ⟨ε, hε, hεU⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨C, hC, hbound⟩ := sigmaFinite_source_free_density_green_bound
    hV hVb hν hU hK.cthickening hεU hUV
  refine ⟨ε / 2, (4 / ε) * C, by positivity, by positivity, ?_⟩
  intro f hfm hfi hfz x hx y hy
  have hball : closedBall x ε ⊆ cthickening ε K := by
    intro z hz
    exact mem_cthickening_of_dist_le z x ε K hx hz
  have hh := (sigmaFinite_integrable_density_transposedGreen_source_free
    hV hVb hν hU hUV hfm hfi hfz).2.mono (hball.trans hεU)
  have hs : ∀ z ∈ sphere x ε, |∫ w, f w * greenFunction V w z ∂ν| ≤
      C * ∫ w, |f w| ∂ν := by
    intro z hz
    exact hbound f hfm hfi hfz z (hball (sphere_subset_closedBall hz))
  have h := harmonic_difference_le hε hh hs hy
  convert h using 1
  ring

#print axioms sigmaFinite_source_free_density_green_local_lipschitz
end HarmonicBalls
