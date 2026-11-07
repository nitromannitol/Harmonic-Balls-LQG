import HarmonicBalls.Proofs.Sec6.GreenUniformBound
import HarmonicBalls.Proofs.Potential.GeneralDomainSourceFreePotential

/-! # Source-free disc potentials

The potential-theoretic infrastructure used here is due to Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter InnerProductSpace
open scoped Topology

/-- The potential of a finite measure restricted to a compact subset of a disc
is continuous away from that set. -/
theorem continuousOn_restricted_greenPotential_ball {R : ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hKB : K ⊆ ball (0 : ℂ) R)
    {ν : Measure ℂ} (hfinite : ν K < ⊤) :
    ContinuousOn (fun z => ∫ y in K, greenFunction (ball 0 R) z y ∂ν)
      (ball 0 R \ K) := by
  let m := ν.restrict K
  let : IsFiniteMeasure m := isFiniteMeasure_restrict.2 hfinite.ne
  intro z hz
  apply ContinuousAt.continuousWithinAt
  obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp (isOpen_ball.sdiff hK.isClosed) z hz
  have hsmall : closedBall z (δ / 2) ⊆ ball (0 : ℂ) R \ K :=
    (closedBall_subset_ball (by linarith)).trans hδsub
  have hdis : Disjoint (closedBall z (δ / 2)) K :=
    disjoint_left.mpr (fun w hw hwK => (hsmall hw).2 hwK)
  obtain ⟨C, hC⟩ := Section6.exists_uniform_bound_greenFunction isBounded_ball
    (isCompact_closedBall z (δ / 2)) hK (hsmall.trans sdiff_subset) hKB hdis
  change Tendsto (fun w => ∫ y, greenFunction (ball 0 R) w y ∂m) (𝓝 z)
    (𝓝 (∫ y, greenFunction (ball 0 R) z y ∂m))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
  · exact Eventually.of_forall fun w => (measurable_greenFunction isOpen_ball w).aestronglyMeasurable
  · filter_upwards [closedBall_mem_nhds z (by linarith : 0 < δ / 2)] with w hw
    filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    simpa only [Real.norm_eq_abs] using hC w hw y hy
  · exact integrable_const C
  · filter_upwards [ae_restrict_mem hK.measurableSet] with y hy
    have hzy : z ≠ y := fun h => hz.2 (h ▸ hy)
    have hc := (continuousOn_greenFunction_ball (hKB hy)).continuousAt
      (isOpen_compl_singleton.mem_nhds (show z ∈ ({y} : Set ℂ)ᶜ by simpa using hzy))
    simpa only [greenFunction_ball_comm R] using hc.tendsto

/-- A finite compactly supported source has a harmonic disc potential away
from its support. -/
theorem harmonicOnNhd_restricted_greenPotential_ball {R : ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hKB : K ⊆ ball (0 : ℂ) R)
    {ν : Measure ℂ} (hfinite : ν K < ⊤) :
    HarmonicOnNhd (fun z => ∫ y in K, greenFunction (ball 0 R) z y ∂ν)
      (ball 0 R \ K) := by
  apply Section6.harmonicOnNhd_restricted_greenPotential_of_kernel isOpen_ball hK hfinite
  · intro y hy
    have hh := (harmonicOnNhd_greenFunction_ball (hKB hy)).mono
      (show ball (0 : ℂ) R \ K ⊆ ball 0 R \ {y} from fun z hz =>
        ⟨hz.1, fun hzy => hz.2 (hzy ▸ hy)⟩)
    simpa only [greenFunction_ball_comm R] using hh
  · exact (measurable_greenFunction_ball_uncurry R).comp (measurable_snd.prodMk measurable_fst)
  · exact continuousOn_restricted_greenPotential_ball hK hKB hfinite
  · intro c r hr hsub
    have hdis : Disjoint (sphere c r) K := disjoint_left.mpr
      (fun z hz hzK => (hsub (sphere_subset_closedBall hz)).2 hzK)
    obtain ⟨C, hC⟩ := Section6.exists_uniform_bound_greenFunction isBounded_ball
      (isCompact_sphere c r) hK (sphere_subset_closedBall.trans (hsub.trans sdiff_subset)) hKB hdis
    exact ⟨C, fun y hy z hz => hC z hz y hy⟩

/-- A compactly concentrated finite source has a harmonic potential off
its concentration set. -/
theorem harmonicOnNhd_greenPotential_ball_of_compact_source
    {R : ℝ} {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball (0 : ℂ) R) (hν : ν Kᶜ = 0) :
    HarmonicOnNhd (greenPotential (ball 0 R) ν) (ball 0 R \ K) := by
  have hae : ∀ᵐ y ∂ν, y ∈ K := by
    rw [ae_iff]
    exact hν
  have hrest : ν.restrict K = ν := Measure.restrict_eq_self_of_ae_mem hae
  have h := harmonicOnNhd_restricted_greenPotential_ball hK hKB (measure_lt_top ν K)
  rw [hrest] at h
  change HarmonicOnNhd (fun z => ∫ y, greenFunction (ball 0 R) z y ∂ν) _
  exact h

/-- The compactly concentrated potential is continuous off its source set. -/
theorem continuousOn_greenPotential_ball_of_compact_source
    {R : ℝ} {K : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball (0 : ℂ) R) (hν : ν Kᶜ = 0) :
    ContinuousOn (greenPotential (ball 0 R) ν) (ball 0 R \ K) :=
  (harmonicOnNhd_greenPotential_ball_of_compact_source hK hKB hν).continuousOn

/-- A compactly concentrated finite source has a harmonic potential on any
open source-free subset of the disc. -/
theorem harmonicOnNhd_greenPotential_ball_of_source_free_open
    {R : ℝ} {K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball (0 : ℂ) R) (hν : ν Kᶜ = 0)
    (hU : IsOpen U) (hUB : U ⊆ ball (0 : ℂ) R) (hνU : ν U = 0) :
    HarmonicOnNhd (greenPotential (ball 0 R) ν) U := by
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
  exact (harmonicOnNhd_greenPotential_ball_of_compact_source hKU
    (sdiff_subset.trans hKB) hcon).mono (fun x hx => ⟨hUB hx, fun h => h.2 hx⟩)

/-- The potential is continuous on an open source-free subset of the disc. -/
theorem continuousOn_greenPotential_ball_of_source_free_open
    {R : ℝ} {K U : Set ℂ} {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hK : IsCompact K) (hKB : K ⊆ ball (0 : ℂ) R) (hν : ν Kᶜ = 0)
    (hU : IsOpen U) (hUB : U ⊆ ball (0 : ℂ) R) (hνU : ν U = 0) :
    ContinuousOn (greenPotential (ball 0 R) ν) U :=
  (harmonicOnNhd_greenPotential_ball_of_source_free_open hK hKB hν hU hUB hνU).continuousOn

#print axioms continuousOn_greenPotential_ball_of_compact_source
#print axioms harmonicOnNhd_greenPotential_ball_of_compact_source
#print axioms harmonicOnNhd_greenPotential_ball_of_source_free_open
#print axioms continuousOn_greenPotential_ball_of_source_free_open

#print axioms continuousOn_restricted_greenPotential_ball
#print axioms harmonicOnNhd_restricted_greenPotential_ball

end HarmonicBalls
