import HarmonicBalls.Proofs.Potential.TranslatedDiscSourceFreeHarmonicity
import HarmonicBalls.Proofs.Potential.TranslatedFiniteSourceDiscCorrection
import HarmonicBalls.Proofs.Potential.GeneralDomainSourceFreePotential

/-! # Source-free whole-plane potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
These analytic results do not close a numbered result of the paper.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace Filter Topology

private theorem integrable_wholePlane_kernel_off_compact
    {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν] {x : ℂ}
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hx : x ∉ K) :
    Integrable (fun y => greenFunction univ x y) ν := by
  have hc : ContinuousOn (newtonKernel x) K := by
    unfold newtonKernel
    refine continuousOn_const.mul (ContinuousOn.log (continuousOn_const.sub continuousOn_id).norm ?_)
    intro y hy
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 (fun h => hx (h ▸ hy)))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  rw [show (fun y => greenFunction univ x y) = newtonKernel x from
    funext (greenFunction_univ_eq_newtonKernel x)]
  refine Integrable.of_bound (measurable_newtonKernel x).aestronglyMeasurable C ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν] with y hy
  exact hC y (by simpa using hy)

/-- A compactly concentrated finite source has harmonic whole-plane potential
outside its concentration set. -/
theorem harmonicOnNhd_greenPotential_univ_of_compact_source
    {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hν : ν Kᶜ = 0) :
    HarmonicOnNhd (greenPotential univ ν) Kᶜ := by
  intro x hx
  obtain ⟨R, hR, hsub⟩ := (hK.union isCompact_singleton).isBounded.subset_ball_lt 0 (0 : ℂ)
  have hKB : K ⊆ ball (0 : ℂ) R := subset_union_left.trans hsub
  have hxB : x ∈ ball (0 : ℂ) R := hsub (mem_union_right _ (mem_singleton x))
  have hνB : ∀ᵐ y ∂ν, y ∈ ball (0 : ℂ) R := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν] with y hy
    exact hKB (by simpa using hy)
  have hlocal : greenPotential univ ν =ᶠ[𝓝 x]
      (greenPotential (ball 0 R) ν + translatedDiscSourceCorrection 0 R ν) := by
    filter_upwards [isOpen_ball.mem_nhds hxB, hK.isClosed.isOpen_compl.mem_nhds hx] with y hyB hyK
    have hatom : ν {y} = 0 := measure_mono_null (by
      intro z hz
      simp only [mem_singleton_iff] at hz
      subst z
      exact hyK) hν
    exact greenPotential_univ_eq_translatedDisc_add_correction hR hνB hyB hatom
      (integrable_wholePlane_kernel_off_compact hK hν hyK)
      (integrable_greenFunction_of_compact_source isOpen_ball hK hKB hν ⟨hyB, hyK⟩)
  apply (harmonicAt_congr_nhds hlocal).2
  exact (harmonicOnNhd_greenPotential_translatedDisc_of_compact_source hK hKB hν x
    ⟨hxB, hx⟩).add ((harmonicOnNhd_translatedDiscSourceCorrection hR hK hKB hν) x hxB)

/-- The whole-plane potential is continuous outside the concentration set. -/
theorem continuousOn_greenPotential_univ_of_compact_source
    {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hν : ν Kᶜ = 0) :
    ContinuousOn (greenPotential univ ν) Kᶜ :=
  (harmonicOnNhd_greenPotential_univ_of_compact_source hK hν).continuousOn

/-- The whole-plane potential is harmonic on any source-free open set. -/
theorem harmonicOnNhd_greenPotential_univ_of_source_free_open
    {K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hU : IsOpen U) (hνU : ν U = 0) :
    HarmonicOnNhd (greenPotential univ ν) U := by
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
  exact (harmonicOnNhd_greenPotential_univ_of_compact_source hKU hcon).mono
    (fun _ hx h => h.2 hx)

/-- The whole-plane potential is continuous on any source-free open set. -/
theorem continuousOn_greenPotential_univ_of_source_free_open
    {K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hU : IsOpen U) (hνU : ν U = 0) :
    ContinuousOn (greenPotential univ ν) U :=
  (harmonicOnNhd_greenPotential_univ_of_source_free_open hK hν hU hνU).continuousOn


end HarmonicBalls
