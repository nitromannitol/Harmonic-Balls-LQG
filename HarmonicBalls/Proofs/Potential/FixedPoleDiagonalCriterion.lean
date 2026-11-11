import HarmonicBalls.Proofs.Potential.TransposedChangedSourceObstruction
import HarmonicBalls.Proofs.Sec5.GeneralDomainInteriorGreen

/-! # Fixed-pole diagonal criterion

The potential-theoretic infrastructure uses work of Leonardo Bonanno. The Green
kernel retains its source-observer order and its prescribed zero diagonal.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter InnerProductSpace
open scoped Topology

/-- A continuous correction exists exactly when the actual harmonic correction
vanishes at the pole. The observation measure records both volume and the pole. -/
theorem exists_continuousAt_fixedPole_correction_iff
    {V : Set ℂ} {z : ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hz : z ∈ V) :
    (∃ a : ℂ → ℝ, ContinuousAt a z ∧
      ∀ᵐ x ∂(volume + Measure.dirac z).restrict V,
        greenPotential univ (Measure.dirac z) x = a x + greenFunction V z x) ↔
      (greatestHarmonicMinorant V (newtonKernelEReal z) z).toReal = 0 := by
  classical
  let H : ℂ → ℝ := fun x => (greatestHarmonicMinorant V (newtonKernelEReal z) x).toReal
  have hH : ContinuousAt H z :=
    ((harmonicOnNhd_greatestHarmonicMinorant_newtonKernel hV hVb hz) z hz).1.continuousAt
  have hoff : ∀ x ∈ V, x ≠ z →
      greenPotential univ (Measure.dirac z) x = H x + greenFunction V z x := by
    intro x hx hxz
    rw [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      greenFunction, ite_eq_left (show z ∈ V ∧ x ∈ V ∧ z ≠ x from ⟨hz, hx, Ne.symm hxz⟩), newtonKernel_comm x z]
    dsimp [H]
    ring
  constructor
  · rintro ⟨a, ha, he⟩
    rw [Measure.restrict_add, ae_add_measure_iff] at he
    have ha0 : a z = 0 := by
      have h := he.2
      rw [restrict_dirac, ite_eq_left hz, ae_dirac_eq] at h
      simp [greenPotential, greenFunction_self] at h
      linarith
    have hae : ∀ᵐ x ∂volume.restrict V, a x = H x := by
      filter_upwards [he.1, ae_restrict_mem hV.measurableSet,
        ae_restrict_of_ae (volume.ae_ne z)] with x hx hxV hxz
      have hh := hoff x hxV hxz
      linarith
    have heq : a z = H z := by
      by_contra hn
      have hnear : {x | a x ≠ H x} ∈ 𝓝 z :=
        (ha.prodMk hH) (isClosed_diagonal.isOpen_compl.mem_nhds hn)
      obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (inter_mem hnear (hV.mem_nhds hz))
      have hsub : ball z r ⊆ V := fun x hx => (hrsub hx).2
      obtain ⟨x, hx, hxeq⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
        (ne_of_gt (Metric.measure_ball_pos volume z hr))
        (ae_restrict_of_ae_restrict_of_subset hsub hae)
      exact (hrsub hx).1 hxeq
    simpa only [← ha0] using heq.symm
  · intro hzero
    refine ⟨H, hH, ?_⟩
    apply ae_restrict_of_forall_mem hV.measurableSet
    intro x hx
    by_cases hxz : x = z
    · subst x
      simp [greenPotential, greenFunction_self, H, hzero]
    · exact hoff x hx hxz


end HarmonicBalls
