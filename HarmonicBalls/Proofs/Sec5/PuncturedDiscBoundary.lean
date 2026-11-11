import HarmonicBalls.Proofs.Sec5.IrregularCompatibilityObstruction

/-! # A punctured-disc reduction for irregular-domain compatibility

The comparison of Green functions below is a hypothesis, not an established
polar-removal theorem. The results locate the remaining potential-theoretic
input and do not assert a counterexample to compatibility.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- If the Green function of a punctured disc agrees off the pole with that
of the disc, it is bounded away from zero near the puncture. -/
theorem frequently_green_pos_punctured_disc_of_green_eq
    {R : ℝ} {z a : ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (hgreen : ∀ x ∈ ball (0 : ℂ) R \ {a}, x ≠ z →
      greenFunction (ball (0 : ℂ) R \ {a}) z x = greenFunction (ball 0 R) z x) :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a,
      c ≤ greenFunction (ball (0 : ℂ) R \ {a}) z x := by
  have hza : z ≠ a := by simpa using hz.2
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  have : (𝓝[ball (0 : ℂ) R \ {a}] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  have hpos := greenFunction_ball_pos hz.1 ha hza
  refine ⟨greenFunction (ball (0 : ℂ) R) z a / 2, by linarith, ?_⟩
  have hcont : ContinuousAt (greenFunction (ball (0 : ℂ) R) z) a :=
    (continuousOn_greenFunction_ball hz.1).continuousAt
      (isOpen_compl_singleton.mem_nhds (show a ≠ z from Ne.symm hza))
  have hnear : ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a,
      greenFunction (ball (0 : ℂ) R) z a / 2 < greenFunction (ball 0 R) z x :=
    (hcont.eventually (Ioi_mem_nhds (show _ < _ from by linarith))).filter_mono nhdsWithin_le_nhds
  have hne : ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a, x ≠ z :=
    (show ∀ᶠ x in 𝓝 a, x ≠ z from
      isOpen_compl_singleton.mem_nhds (show a ≠ z from Ne.symm hza)).filter_mono
        nhdsWithin_le_nhds
  have hevent : ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a,
      greenFunction (ball (0 : ℂ) R) z a / 2 ≤
        greenFunction (ball (0 : ℂ) R \ {a}) z x := by
    filter_upwards [hnear, hne, self_mem_nhdsWithin] with x hx hzx hxU
    rw [hgreen x hxU hzx]
    exact le_of_lt hx
  exact hevent.frequently

/-- Under the Green-function comparison, agreement with a compactly
contained set forces the punctured-disc least supersolution to be inadmissible.
This implication does not establish either Green-function comparison or cluster
compatibility. -/
theorem not_admissible_punctured_disc_of_compact_compatibility
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ} {A : Set ℂ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 < t)
    (hgreen : ∀ x ∈ ball (0 : ℂ) R \ {a}, x ≠ z →
      greenFunction (ball (0 : ℂ) R \ {a}) z x = greenFunction (ball 0 R) z x)
    (hA : closure A ⊆ ball (0 : ℂ) R \ {a})
    (heq : closure A = closure (clusterOn μ (ball (0 : ℂ) R \ {a}) z t)) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t := by
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  have haU : a ∉ ball (0 : ℂ) R \ {a} := by simp
  obtain ⟨c, hc, hG⟩ := frequently_green_pos_punctured_disc_of_green_eq ha hz hgreen
  exact not_mem_supersolutionsOn_of_regularized_compact_compatibility
    hz hac haU ht hc hG hA heq

end HarmonicBalls
