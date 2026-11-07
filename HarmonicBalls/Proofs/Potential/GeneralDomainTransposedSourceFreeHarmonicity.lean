import HarmonicBalls.Proofs.Sec6.GreenUniformBound
import HarmonicBalls.Proofs.Potential.BoundedDomainGreenMeasurability

/-! # Source-free transposed Green integrals

The potential-theoretic infrastructure used here is due to Leonardo Bonanno.
The order of the arguments is retained: no Green reciprocity is assumed.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter InnerProductSpace
open scoped Topology

/-- The transposed Green integral of a finite restricted source is continuous
outside the compact source set. -/
theorem continuousOn_restricted_transposed_greenIntegral {V K : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hKV : K ⊆ V) {ν : Measure ℂ} (hfinite : ν K < ⊤) :
    ContinuousOn (fun x => ∫ y in K, greenFunction V y x ∂ν) (V \ K) := by
  let m := ν.restrict K
  let : IsFiniteMeasure m := isFiniteMeasure_restrict.2 hfinite.ne
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (hV.sdiff hK.isClosed) x hx
  have hsmall : closedBall x (δ / 2) ⊆ V \ K :=
    (closedBall_subset_ball (by linarith)).trans hδsub
  have hdis : Disjoint K (closedBall x (δ / 2)) :=
    disjoint_left.mpr (fun _ hy hw => (hsmall hw).2 hy)
  obtain ⟨C, hC⟩ := Section6.exists_uniform_bound_greenFunction hVb hK
    (isCompact_closedBall x (δ / 2)) hKV (hsmall.trans sdiff_subset) hdis
  change Tendsto (fun w => ∫ y, greenFunction V y w ∂m) (𝓝 x)
    (𝓝 (∫ y, greenFunction V y x ∂m))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall fun w =>
      ((measurable_greenFunction_uncurry hV).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds x (by linarith : 0 < δ / 2)] with w hw
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    simpa only [Real.norm_eq_abs] using hC y hy w hw
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    have hxy : x ≠ y := fun h => hx.2 (h ▸ hy)
    have hc := (Section6.harmonicOnNhd_greenFunction_right hV hVb (hKV hy)
      x ⟨hx.1, by simpa using hxy⟩).1.continuousAt
    exact hc.tendsto

/-- The transposed Green integral is harmonic outside a compact restricted source. -/
theorem harmonicOnNhd_restricted_transposed_greenIntegral {V K : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hK : IsCompact K) (hKV : K ⊆ V) {ν : Measure ℂ} (hfinite : ν K < ⊤) :
    HarmonicOnNhd (fun x => ∫ y in K, greenFunction V y x ∂ν) (V \ K) := by
  classical
  let m := ν.restrict K
  let : IsFiniteMeasure m := isFiniteMeasure_restrict.2 hfinite.ne
  let F : ℂ → ℂ → ℝ := fun y x => K.indicator (fun y => greenFunction V y x) y
  have hF : ∀ y, HarmonicOnNhd (F y) (V \ K) := by
    intro y
    by_cases hy : y ∈ K
    · simpa only [F, indicator_of_mem hy] using
        (Section6.harmonicOnNhd_greenFunction_right hV hVb (hKV hy)).mono
          (show V \ K ⊆ V \ {y} from fun x hx => ⟨hx.1, fun h => hx.2 (h ▸ hy)⟩)
    · simpa only [F, indicator_of_notMem hy] using harmonicOnNhd_const (0 : ℝ)
  have hFm : Measurable (Function.uncurry F) := by
    have heq : Function.uncurry F = (K ×ˢ (univ : Set ℂ)).indicator
        (fun p : ℂ × ℂ => greenFunction V p.1 p.2) := by
      funext p
      by_cases hp : p.1 ∈ K <;> simp [F, Function.uncurry, hp]
    rw [heq]
    exact (measurable_greenFunction_uncurry hV).indicator (hK.measurableSet.prod MeasurableSet.univ)
  have heq : (fun x => ∫ y, F y x ∂m) =
      fun x => ∫ y in K, greenFunction V y x ∂ν := by
    funext x
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    exact indicator_of_mem hy _
  rw [← heq]
  apply Section6.harmonicOnNhd_integral_of_circle_bounds (hV.sdiff hK.isClosed) hF hFm
  · rw [heq]
    exact continuousOn_restricted_transposed_greenIntegral hV hVb hK hKV hfinite
  · intro c r hr hsub
    have hdis : Disjoint K (sphere c r) := disjoint_left.mpr
      (fun _ hy hx => (hsub (sphere_subset_closedBall hx)).2 hy)
    obtain ⟨C, hC⟩ := Section6.exists_uniform_bound_greenFunction hVb hK
      (isCompact_sphere c r) hKV (sphere_subset_closedBall.trans (hsub.trans sdiff_subset)) hdis
    refine ⟨max C 0, ?_⟩
    intro y x hx
    by_cases hy : y ∈ K
    · simpa only [F, indicator_of_mem hy] using (hC y hy x hx).trans (le_max_left C 0)
    · simpa only [F, indicator_of_notMem hy, abs_zero] using le_max_right C 0

/-- A compactly concentrated finite source has a harmonic transposed Green integral off its concentration set. -/
theorem harmonicOnNhd_transposed_greenIntegral_of_compact_source
    {V K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hK : IsCompact K)
    (hKV : K ⊆ V) (hν : ν Kᶜ = 0) :
    HarmonicOnNhd (fun x => ∫ y, greenFunction V y x ∂ν) (V \ K) := by
  have hae : ∀ᵐ y ∂ν, y ∈ K := by rw [ae_iff]; exact hν
  have hrest : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem hae
  have h := harmonicOnNhd_restricted_transposed_greenIntegral hV hVb hK hKV (measure_lt_top ν K)
  rw [hrest] at h
  exact h

/-- The transposed Green integral is harmonic on an open set of zero source mass. -/
theorem harmonicOnNhd_transposed_greenIntegral_of_source_free_open
    {V K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hK : IsCompact K)
    (hKV : K ⊆ V) (hν : ν Kᶜ = 0) (hU : IsOpen U) (hUV : U ⊆ V)
    (hνU : ν U = 0) :
    HarmonicOnNhd (fun x => ∫ y, greenFunction V y x ∂ν) U := by
  have hKU : IsCompact (K \ U) := hK.inter_right hU.isClosed_compl
  have hcon : ν (K \ U)ᶜ = 0 := by
    apply measure_mono_null (show (K \ U)ᶜ ⊆ Kᶜ ∪ U from by
      intro y hy
      by_cases hyK : y ∈ K
      · right
        by_contra hyU
        exact hy ⟨hyK, hyU⟩
      · exact Or.inl hyK)
    exact measure_union_null hν hνU
  exact (harmonicOnNhd_transposed_greenIntegral_of_compact_source hV hVb hKU
    (sdiff_subset.trans hKV) hcon).mono (fun x hx => ⟨hUV hx, fun h => h.2 hx⟩)

/-- The transposed Green integral is continuous off a compact concentration set. -/
theorem continuousOn_transposed_greenIntegral_of_compact_source
    {V K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hK : IsCompact K)
    (hKV : K ⊆ V) (hν : ν Kᶜ = 0) :
    ContinuousOn (fun x => ∫ y, greenFunction V y x ∂ν) (V \ K) :=
  (harmonicOnNhd_transposed_greenIntegral_of_compact_source hV hVb hK hKV hν).continuousOn

/-- The transposed Green integral is continuous on an open source-free set. -/
theorem continuousOn_transposed_greenIntegral_of_source_free_open
    {V K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hK : IsCompact K)
    (hKV : K ⊆ V) (hν : ν Kᶜ = 0) (hU : IsOpen U) (hUV : U ⊆ V)
    (hνU : ν U = 0) :
    ContinuousOn (fun x => ∫ y, greenFunction V y x ∂ν) U :=
  (harmonicOnNhd_transposed_greenIntegral_of_source_free_open hV hVb hK hKV hν hU hUV hνU).continuousOn

#print axioms continuousOn_transposed_greenIntegral_of_compact_source
#print axioms continuousOn_transposed_greenIntegral_of_source_free_open
#print axioms continuousOn_restricted_transposed_greenIntegral
#print axioms harmonicOnNhd_restricted_transposed_greenIntegral
#print axioms harmonicOnNhd_transposed_greenIntegral_of_compact_source
#print axioms harmonicOnNhd_transposed_greenIntegral_of_source_free_open

end HarmonicBalls
