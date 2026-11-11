import HarmonicBalls.Proofs.Potential.DiscChangedSourceObstruction
import HarmonicBalls.Proofs.Potential.GeneralDomainTransposedFiniteSourceLaplacian
import HarmonicBalls.Proofs.Potential.FiniteSourceTransposedSourceFreeHarmonicity

/-! # Changed-source obstruction for transposed Green integrals

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
The source is the first argument of the Green kernel throughout.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter InnerProductSpace Laplacian
open scoped Topology

/-- The kernel is integrable against a finite source away from an open source-free set. -/
theorem integrable_transposed_green_of_source_free
    {V U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hνV : ν Vᶜ = 0)
    (hU : IsOpen U) (hUV : U ⊆ V) (hνU : ν U = 0) {x : ℂ} (hx : x ∈ U) :
    Integrable (fun y => greenFunction V y x) ν := by
  obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free
    hVb hU isCompact_singleton (singleton_subset_iff.mpr hx)
    (singleton_subset_iff.mpr (hUV hx))
  have hae : ∀ᵐ y ∂ν, y ∈ V \ U := by
    rw [ae_iff]
    apply measure_mono_null (show (V \ U)ᶜ ⊆ Vᶜ ∪ U from by
      intro y hy
      by_cases hv : y ∈ V
      · right
        by_contra hu
        exact hy ⟨hv, hu⟩
      · exact Or.inl hv)
    exact measure_union_null hνV hνU
  apply (integrable_const (max C 0)).mono' 
    ((measurable_greenFunction_uncurry hV).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  filter_upwards [hae] with y hy
  simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using (hC y hy x (mem_singleton x)).trans (le_max_left C 0)

/-- The prescribed diagonal prevents a continuous correction to the whole-plane
point-source potential on a large observation disc. -/
theorem no_transposed_continuous_correction_for_large_observation
    {V : Set ℂ} (hV : Bornology.IsBounded V) (hsub : ball (0 : ℂ) 2 ⊆ V) :
    ¬ ∃ a : ℂ → ℝ, ContinuousAt a 0 ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
        greenPotential univ (Measure.dirac 0) x = a x + greenFunction V 0 x) := by
  classical
  rintro ⟨a, ha, hae⟩
  rw [Measure.restrict_add, ae_add_measure_iff] at hae
  have hzero : a 0 = 0 := by
    have h := hae.2
    rw [restrict_dirac, ite_eq_left (mem_ball_self (by norm_num : (0 : ℝ) < 2)),
      ae_dirac_eq] at h
    simp [greenPotential, greenFunction_self] at h
    linarith
  let c : ℝ := (2 * Real.pi)⁻¹ * Real.log 2
  have hc : 0 < c := mul_pos (by positivity) (Real.log_pos (by norm_num))
  have hbound : ∀ᵐ x ∂volume.restrict (ball (0 : ℂ) 2), a x ≤ -c := by
    filter_upwards [hae.1, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with x hx hxb hx0
    have hm := Section6.greenFunction_le_of_subset hsub hV (0 : ℂ) x
    have hb := greenPotential_dirac_zero_ball (by norm_num : (0 : ℝ) < 2) hxb hx0
    simp only [greenPotential, integral_dirac] at hb hx
    simp only [greenFunction_univ_eq_newtonKernel, newtonKernel, sub_zero] at hx
    rw [greenFunction_ball_comm 2 0 x] at hm
    dsimp [c] at *
    linarith
  have hnear : {x | -c < a x} ∈ nhds (0 : ℂ) :=
    ha (Ioi_mem_nhds (by rw [hzero]; linarith))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let t := min r 2
  have ht : 0 < t := lt_min hr (by norm_num)
  have htsub : ball (0 : ℂ) t ⊆ ball 0 2 := ball_subset_ball (min_le_right _ _)
  have htnear : ball (0 : ℂ) t ⊆ {x | -c < a x} :=
    (ball_subset_ball (min_le_left _ _)).trans hrsub
  obtain ⟨x, hx, hxa⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt (Metric.measure_ball_pos volume (0 : ℂ) ht))
    (ae_restrict_of_ae_restrict_of_subset htsub hbound)
  exact (not_lt_of_ge hxa) (htnear hx)

/-- Finite sources carried by the domain cannot represent the negative whole-plane point
potential by literal transposed Green integrals on the observation disc. -/
theorem no_transposed_changed_source_for_large_observation
    {V : Set ℂ} {η₁ η₂ : Measure ℂ} {q : ℂ → ℝ}
    [IsFiniteMeasure η₁] [IsFiniteMeasure η₂]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hsub : ball (0 : ℂ) 2 ⊆ V)
    (hη₁V : η₁ Vᶜ = 0) (hη₂V : η₂ Vᶜ = 0)
    (hzero : η₁ (ball 0 2) = 0) (hq : HarmonicOnNhd q V) :
    ¬ (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
      -greenPotential univ (Measure.dirac 0) x =
        q x + (∫ y, greenFunction V y x ∂η₁) - (∫ y, greenFunction V y x ∂η₂)) := by
  have h0 : (0 : ℂ) ∈ ball 0 (2 : ℝ) := mem_ball_self (by norm_num)
  have hΔ := hasLaplacian_changedSource_on_source_free isOpen_ball hsub hzero hq
    (hasLaplacian_generalDomain_transposedGreenPotential hV hVb (ae_iff.mpr hη₁V))
    (hasLaplacian_generalDomain_transposedGreenPotential hV hVb (ae_iff.mpr hη₂V))
  intro heq
  have hvol : -greenPotential univ (Measure.dirac (0 : ℂ)) =ᵐ[
      volume.restrict (ball 0 (2 : ℝ))]
      (q + (fun x => ∫ y, greenFunction V y x ∂η₁) -
        (fun x => ∫ y, greenFunction V y x ∂η₂)) := by
    rw [Measure.restrict_add, ae_add_measure_iff] at heq
    exact heq.1
  have hres := negative_source_residual_null_of_ae_and_hasLaplacian
    isOpen_ball h0 (inferInstance : IsLocallyFiniteMeasure η₂) hΔ hvol
  have hatom := negative_source_unit_atom_of_ae_dirac_and_hasLaplacian
    isOpen_ball h0 (inferInstance : IsLocallyFiniteMeasure η₂) hΔ hvol
  have hsplit := measure_eq_dirac_add_restrict_compl_of_singleton_eq_one hatom
  have hresV : (η₂.restrict {0}ᶜ) Vᶜ = 0 :=
    le_antisymm (((Measure.restrict_le_self : η₂.restrict {0}ᶜ ≤ η₂) Vᶜ).trans_eq hη₂V) bot_le
  have h₁c := continuousOn_transposed_greenIntegral_of_finite_source
    hV hVb hη₁V isOpen_ball hsub hzero
  have h₂c := continuousOn_transposed_greenIntegral_of_finite_source
    hV hVb hresV isOpen_ball hsub hres
  have hqc : ContinuousAt q 0 := (hq.continuousOn 0 (hsub h0)).continuousAt
    (hV.mem_nhds (hsub h0))
  apply no_transposed_continuous_correction_for_large_observation hVb hsub
  refine ⟨fun x => -q x - (∫ y, greenFunction V y x ∂η₁) +
      (∫ y, greenFunction V y x ∂(η₂.restrict {0}ᶜ)),
    (hqc.neg.sub (h₁c.continuousAt (isOpen_ball.mem_nhds h0))).add
      (h₂c.continuousAt (isOpen_ball.mem_nhds h0)), ?_⟩
  filter_upwards [heq, ae_restrict_mem measurableSet_ball] with x hx hxball
  have hi := integrable_transposed_green_of_source_free hV hVb hresV isOpen_ball hsub hres hxball
  have hd : Integrable (fun y => greenFunction V y x) (Measure.dirac (0 : ℂ)) :=
    integrable_dirac enorm_lt_top
  rw [hsplit, integral_add_measure hd hi, integral_dirac] at hx
  linarith



end HarmonicBalls
