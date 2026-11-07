import HarmonicBalls.Proofs.Potential.GeneralDomainTransposedSourceFreeHarmonicity

/-! # Source-free transposed Green integrals for finite sources

The potential-theoretic infrastructure used here is due to Leonardo Bonanno.
No Green reciprocity or compact concentration inside the domain is assumed.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter InnerProductSpace
open scoped Topology

/-- An enclosing disc bounds the kernel uniformly between a compact observer
set and all sources outside an open neighborhood of that set. -/
theorem exists_uniform_bound_transposed_green_of_source_free
    {V U L : Set ℂ} (hVb : Bornology.IsBounded V) (hU : IsOpen U)
    (hL : IsCompact L) (hLU : L ⊆ U) (hLV : L ⊆ V) :
    ∃ C : ℝ, ∀ y ∈ V \ U, ∀ x ∈ L, |greenFunction V y x| ≤ C := by
  let K := closure V \ U
  have hK : IsCompact K := hVb.isCompact_closure.inter_right hU.isClosed_compl
  obtain ⟨R, hR⟩ := hVb.closure.subset_ball (0 : ℂ)
  have hKD : K ⊆ ball (0 : ℂ) R := fun y hy => hR hy.1
  have hLD : L ⊆ ball (0 : ℂ) R := hLV.trans (subset_closure.trans hR)
  have hdis : Disjoint K L := disjoint_left.mpr fun y hy hyL => hy.2 (hLU hyL)
  obtain ⟨C, hC⟩ := Section6.exists_uniform_bound_greenFunction isBounded_ball hK hL hKD hLD hdis
  refine ⟨C, ?_⟩
  intro y hy x hx
  rw [abs_of_nonneg (greenFunction_nonneg hVb y x)]
  calc
    greenFunction V y x ≤ greenFunction (ball (0 : ℂ) R) y x :=
      Section6.greenFunction_le_of_subset (subset_closure.trans hR) isBounded_ball y x
    _ ≤ |greenFunction (ball (0 : ℂ) R) y x| := le_abs_self _
    _ ≤ C := hC y ⟨subset_closure hy.1, hy.2⟩ x hx

/-- A finite source has a harmonic transposed Green integral on any open
source-free subset of a bounded open domain. -/
theorem harmonicOnNhd_transposed_greenIntegral_of_finite_source
    {V U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hνV : ν Vᶜ = 0) (hU : IsOpen U) (hUV : U ⊆ V) (hνU : ν U = 0) :
    HarmonicOnNhd (fun x => ∫ y, greenFunction V y x ∂ν) U := by
  classical
  let S := V \ U
  let F : ℂ → ℂ → ℝ := fun y x => S.indicator (fun y => greenFunction V y x) y
  have hF : ∀ y, HarmonicOnNhd (F y) U := by
    intro y
    by_cases hy : y ∈ S
    · simpa only [F, indicator_of_mem hy] using
        (Section6.harmonicOnNhd_greenFunction_right hV hVb hy.1).mono
          (show U ⊆ V \ {y} from fun x hx => ⟨hUV hx, fun h => hy.2 (h ▸ hx)⟩)
    · simpa only [F, indicator_of_notMem hy] using harmonicOnNhd_const (0 : ℝ)
  have hFm : Measurable (Function.uncurry F) := by
    have heq : Function.uncurry F = (S ×ˢ (univ : Set ℂ)).indicator
        (fun p : ℂ × ℂ => greenFunction V p.1 p.2) := by
      funext p
      by_cases hp : p.1 ∈ S <;> simp [F, Function.uncurry, hp]
    rw [heq]
    exact (measurable_greenFunction_uncurry hV).indicator
      ((hV.measurableSet.diff hU.measurableSet).prod MeasurableSet.univ)
  have hae : ∀ᵐ y ∂ν, y ∈ S := by
    rw [ae_iff]
    apply measure_mono_null (show Sᶜ ⊆ Vᶜ ∪ U from by
      intro y hy
      by_cases hv : y ∈ V
      · right
        by_contra hu
        exact hy ⟨hv, hu⟩
      · exact Or.inl hv)
    exact measure_union_null hνV hνU
  have heq : (fun x => ∫ y, F y x ∂ν) =
      fun x => ∫ y, greenFunction V y x ∂ν := by
    funext x
    apply integral_congr_ae
    filter_upwards [hae] with y hy
    exact indicator_of_mem hy _
  have hcont : ContinuousOn (fun x => ∫ y, F y x ∂ν) U := by
    intro x hx
    apply ContinuousAt.continuousWithinAt
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hU x hx
    have hsmall : closedBall x (δ / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hδsub
    obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free
      hVb hU (isCompact_closedBall x (δ / 2)) hsmall (hsmall.trans hUV)
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => max C 0)
    · exact Eventually.of_forall fun w =>
        (hFm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    · filter_upwards [closedBall_mem_nhds x (by linarith : 0 < δ / 2)] with w hw
      filter_upwards [] with y
      by_cases hy : y ∈ S
      · simpa only [F, indicator_of_mem hy, Real.norm_eq_abs] using
          (hC y hy w hw).trans (le_max_left C 0)
      · simpa only [F, indicator_of_notMem hy, norm_zero] using le_max_right C 0
    · exact integrable_const _
    · exact Eventually.of_forall fun y => (hF y x hx).1.continuousAt.tendsto
  rw [← heq]
  apply Section6.harmonicOnNhd_integral_of_circle_bounds hU hF hFm hcont
  intro c r hr hsub
  obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free
    hVb hU (isCompact_sphere c r) (sphere_subset_closedBall.trans hsub)
      (sphere_subset_closedBall.trans (hsub.trans hUV))
  refine ⟨max C 0, ?_⟩
  intro y x hx
  by_cases hy : y ∈ S
  · simpa only [F, indicator_of_mem hy] using (hC y hy x hx).trans (le_max_left C 0)
  · simpa only [F, indicator_of_notMem hy, abs_zero] using le_max_right C 0

/-- The same finite-source transposed Green integral is continuous. -/
theorem continuousOn_transposed_greenIntegral_of_finite_source
    {V U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hνV : ν Vᶜ = 0) (hU : IsOpen U) (hUV : U ⊆ V) (hνU : ν U = 0) :
    ContinuousOn (fun x => ∫ y, greenFunction V y x ∂ν) U :=
  (harmonicOnNhd_transposed_greenIntegral_of_finite_source hV hVb hνV hU hUV hνU).continuousOn

#print axioms exists_uniform_bound_transposed_green_of_source_free
#print axioms harmonicOnNhd_transposed_greenIntegral_of_finite_source
#print axioms continuousOn_transposed_greenIntegral_of_finite_source

end HarmonicBalls
