import HarmonicBalls.Proofs.Sec6.HarmonicIntegral
import HarmonicBalls.Proofs.Potential.BoundedSubharmonicRepresentatives
import HarmonicBalls.Proofs.Potential.DiscFiniteSourceLaplacian

/-!
# Finite-source disc correction

This analytic leaf uses the potential-theoretic work of Leonardo Bonanno. It
integrates the off-diagonal disc kernel identity; it is not a numbered-result
closure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter

/-- The explicit harmonic correction integrated against the source. -/
noncomputable def discSourceCorrection (R : ℝ) (ν : Measure ℂ) (x : ℂ) : ℝ :=
  ∫ y, greatestHarmonicMinorantBall R y x ∂ν

/-- At an uncharged interior point, integrability of both kernels makes the
integrated off-diagonal identity valid without changing totalized integrals. -/
theorem greenPotential_univ_eq_ball_add_discSourceCorrection
    {R : ℝ} {ν : Measure ℂ} {x : ℂ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ ball (0 : ℂ) R) (hx : x ∈ ball (0 : ℂ) R)
    (hatom : ν {x} = 0)
    (huniv : Integrable (fun y => greenFunction univ x y) ν)
    (hball : Integrable (fun y => greenFunction (ball 0 R) x y) ν) :
    greenPotential univ ν x = greenPotential (ball 0 R) ν x + discSourceCorrection R ν x := by
  have hne : ∀ᵐ y ∂ν, x ≠ y := by
    rw [ae_iff]
    simpa [eq_comm] using hatom
  have heq : (fun y => greatestHarmonicMinorantBall R y x) =ᵐ[ν]
      fun y => greenFunction univ x y - greenFunction (ball 0 R) x y := by
    filter_upwards [hν, hne] with y hy hxy
    have h := greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR hy hx hxy
    simp only [greenPotential, integral_dirac] at h
    linarith
  have hc : discSourceCorrection R ν x =
      (∫ y, greenFunction univ x y ∂ν) -
        (∫ y, greenFunction (ball 0 R) x y ∂ν) := by
    rw [discSourceCorrection, integral_congr_ae heq, integral_sub huniv hball]
  change (∫ y, greenFunction univ x y ∂ν) =
    (∫ y, greenFunction (ball 0 R) x y ∂ν) + discSourceCorrection R ν x
  rw [hc]
  ring

/-- The explicit correction is continuous jointly in source and observer
when both lie in the disc. -/
theorem continuousOn_discCorrectionKernel {R : ℝ} (hR : 0 < R) :
    ContinuousOn (fun p : ℂ × ℂ => greatestHarmonicMinorantBall R p.1 p.2)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := by
  have hf : Continuous (fun p : ℂ × ℂ => ‖(R : ℂ) ^ 2 - starRingEnd ℂ p.1 * p.2‖) := by
    fun_prop
  have hl : ContinuousOn (fun p : ℂ × ℂ => Real.log ‖(R : ℂ) ^ 2 - starRingEnd ℂ p.1 * p.2‖)
      (ball (0 : ℂ) R ×ˢ ball (0 : ℂ) R) := by
    apply ContinuousOn.log hf.continuousOn
    intro p hp
    exact (norm_sub_conj_mul_pos hR (mem_ball_zero_iff.1 hp.1)
      (mem_ball_zero_iff.1 hp.2).le).ne'
  simpa only [greatestHarmonicMinorantBall, Pi.sub_apply] using
    (hl.sub continuousOn_const).const_mul (-(2 * Real.pi)⁻¹)

/-- The correction kernel is Bochner integrable against a finite compact source
at every interior observer. -/
theorem integrable_discCorrectionKernel {R : ℝ} {K : Set ℂ} {ν : Measure ℂ}
    [IsFiniteMeasure ν] (hR : 0 < R) (hK : IsCompact K)
    (hKB : K ⊆ ball (0 : ℂ) R) (hν : ν Kᶜ = 0)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) R) :
    Integrable (fun y => greatestHarmonicMinorantBall R y x) ν := by
  have hc := (continuousOn_discCorrectionKernel hR).mono
    (Set.prod_mono hKB (singleton_subset_iff.mpr hx))
  obtain ⟨C, hC⟩ := (hK.prod isCompact_singleton).exists_bound_of_continuousOn hc
  have hm : Measurable (fun y => greatestHarmonicMinorantBall R y x) := by
    unfold greatestHarmonicMinorantBall
    fun_prop
  apply Integrable.mono' (integrable_const C) hm.aestronglyMeasurable
  have hae : ∀ᵐ y ∂ν, y ∈ K := by rw [ae_iff]; exact hν
  filter_upwards [hae] with y hy
  exact hC (y, x) ⟨hy, mem_singleton x⟩

/-- Integration preserves harmonicity for a compactly concentrated finite source. -/
theorem harmonicOnNhd_discSourceCorrection {R : ℝ} {K : Set ℂ} {ν : Measure ℂ}
    [IsFiniteMeasure ν] (hR : 0 < R) (hK : IsCompact K)
    (hKB : K ⊆ ball (0 : ℂ) R) (hν : ν Kᶜ = 0) :
    HarmonicOnNhd (discSourceCorrection R ν) (ball 0 R) := by
  let F : ℂ → ℂ → ℝ := fun y x => K.indicator (fun y => greatestHarmonicMinorantBall R y x) y
  have hae : ∀ᵐ y ∂ν, y ∈ K := by rw [ae_iff]; exact hν
  have hF : ∀ y, HarmonicOnNhd (F y) (ball 0 R) := by
    intro y
    by_cases hy : y ∈ K
    · simpa only [F, indicator_of_mem hy] using
        (isHarmonicMinorant_greatestHarmonicMinorantBall (hKB hy)).1
    · simpa only [F, indicator_of_notMem hy] using harmonicOnNhd_const (0 : ℝ)
  have hm : Measurable (Function.uncurry F) := by
    have hm0 : Measurable (fun p : ℂ × ℂ => greatestHarmonicMinorantBall R p.1 p.2) := by
      unfold greatestHarmonicMinorantBall
      fun_prop
    have heq : Function.uncurry F = (K ×ˢ (univ : Set ℂ)).indicator
        (fun p : ℂ × ℂ => greatestHarmonicMinorantBall R p.1 p.2) := by
      funext p
      by_cases hp : p.1 ∈ K <;> simp [F, Function.uncurry, hp]
    rw [heq]
    exact hm0.indicator (hK.measurableSet.prod MeasurableSet.univ)
  have heq : (fun x => ∫ y, F y x ∂ν) = discSourceCorrection R ν := by
    funext x
    apply integral_congr_ae
    filter_upwards [hae] with y hy
    simp only [F, indicator_of_mem hy]
  have hc : ContinuousOn (fun x => ∫ y, F y x ∂ν) (ball 0 R) := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp isOpen_ball x hx
    have hsub : closedBall x (δ / 2) ⊆ ball (0 : ℂ) R :=
      (closedBall_subset_ball (by linarith)).trans hδsub
    have hcprod := (continuousOn_discCorrectionKernel hR).mono (Set.prod_mono hKB hsub)
    obtain ⟨C, hC⟩ := (hK.prod (isCompact_closedBall x (δ / 2))).exists_bound_of_continuousOn hcprod
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => max C 0)
    · exact Filter.Eventually.of_forall fun w => (hm.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : ℂ => w)))).aestronglyMeasurable
    · filter_upwards [closedBall_mem_nhds x (by linarith : 0 < δ / 2)] with w hw
      filter_upwards [hae] with y hy
      simpa only [F, indicator_of_mem hy, Real.norm_eq_abs] using (hC (y, w) ⟨hy, hw⟩).trans (le_max_left C 0)
    · exact integrable_const _
    · filter_upwards [hae] with y hy
      have hyh := (hF y x hx).1.continuousAt.tendsto
      exact hyh
  rw [← heq]
  apply Section6.harmonicOnNhd_integral_of_circle_bounds isOpen_ball hF hm hc
  intro c r hr hsub
  have hcprod := (continuousOn_discCorrectionKernel hR).mono
    (Set.prod_mono hKB (sphere_subset_closedBall.trans hsub))
  obtain ⟨C, hC⟩ := (hK.prod (isCompact_sphere c r)).exists_bound_of_continuousOn hcprod
  refine ⟨max C 0, ?_⟩
  intro y z hz
  by_cases hy : y ∈ K
  · simpa only [F, indicator_of_mem hy, Real.norm_eq_abs] using (hC (y, z) ⟨hy, hz⟩).trans (le_max_left C 0)
  · simpa only [F, indicator_of_notMem hy, abs_zero] using le_max_right C 0

/-- Both kernels are integrable, and the correction identity holds, at
planar-almost every interior point. -/
theorem ae_greenPotential_univ_eq_ball_add_discSourceCorrection
    {R : ℝ} {ν : Measure ℂ} [IsFiniteMeasure ν] (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ ball (0 : ℂ) R) :
    ∀ᵐ x ∂volume.restrict (ball (0 : ℂ) R),
      Integrable (fun y => greenFunction univ x y) ν ∧
      Integrable (fun y => greenFunction (ball 0 R) x y) ν ∧
      ν {x} = 0 ∧
      greenPotential univ ν x = greenPotential (ball 0 R) ν x + discSourceCorrection R ν x := by
  have hνc : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R :=
    hν.mono fun _ hy => ball_subset_closedBall hy
  obtain ⟨_, _, r₀, hr₀, hg⟩ := volumeGrowth_volume R
  have hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      volume (ball z r) ≤ ENNReal.ofReal (r ^ (1 : ℝ)) := by
    intro r hr hrr z hz
    exact (hg r hr hrr z hz).2
  have hn := ae_newtonKernel_and_atom_of_upper (ν := ν) le_rfl hR hr₀
    (by norm_num : (0 : ℝ) < 1) hup (measure_ball_lt_top (μ := volume)).ne hνc
  have hb := (disc_green_integrable_product_volume hR hνc).swap.prod_right_ae
  filter_upwards [hn, hb, ae_restrict_mem measurableSet_ball] with x hx hbx hxR
  have hu : Integrable (fun y => greenFunction univ x y) ν := by
    simpa only [greenFunction_univ_eq_newtonKernel] using hx.1
  have hi : Integrable (fun y => greenFunction (ball 0 R) x y) ν := by
    simpa only [Function.comp_apply, Prod.swap_prod_mk, greenFunction_ball_comm R] using hbx
  exact ⟨hu, hi, hx.2, greenPotential_univ_eq_ball_add_discSourceCorrection hR hν hxR hx.2 hu hi⟩

#print axioms continuousOn_discCorrectionKernel
#print axioms integrable_discCorrectionKernel
#print axioms harmonicOnNhd_discSourceCorrection
#print axioms greenPotential_univ_eq_ball_add_discSourceCorrection
#print axioms ae_greenPotential_univ_eq_ball_add_discSourceCorrection

end HarmonicBalls
