import HarmonicBalls.Defs.LQGMetric

/-! # Measurability of path length under lower semicontinuity

Let `D ω` be a family of distance functions on `ℂ` such that `ω ↦ D ω x y` is measurable for every
pair of points. The length of a fixed path is measurable when every `D ω` is lower semicontinuous on
`ℂ × ℂ`, and almost everywhere measurable when `D ω` is lower semicontinuous for almost every `ω`.

The length is the supremum over partitions of the partition sums. For a fixed number of partition
points, the partition sum is lower semicontinuous in the partition, and the space of partitions is
second countable, so this supremum is measurable in `ω`.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- For a pointwise measurable family of lower semicontinuous distance functions, the length of a
fixed path is measurable. -/
theorem measurable_pathLength_of_lowerSemicontinuous
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hlsc : ∀ ω, LowerSemicontinuous fun q : ℂ × ℂ => D ω q.1 q.2)
    {x y : ℂ} (p : Path x y) : Measurable fun ω => pathLength (D ω) p := by
  let T := {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1}
  have : SecondCountableTopology T :=
    TopologicalSpace.secondCountableTopology_induced T (ℕ → ℝ) Subtype.val
  have key : ∀ n : ℕ, Measurable (⨆ u : T, fun ω =>
      ∑ i ∈ Finset.range n, ENNReal.ofReal (D ω (p.extend (u.1 (i + 1))) (p.extend (u.1 i)))) := by
    intro n
    refine measurable_iSup_of_lowerSemicontinuous (fun u => ?_) (fun ω => ?_)
    · exact Finset.measurable_sum _ fun i _ => (hD _ _).ennreal_ofReal
    · refine lowerSemicontinuous_sum fun i _ => ?_
      have hc : Continuous fun u : T => (p.extend (u.1 (i + 1)), p.extend (u.1 i)) :=
        (p.continuous_extend.comp ((continuous_apply (i + 1)).comp continuous_subtype_val)).prodMk
          (p.continuous_extend.comp ((continuous_apply i).comp continuous_subtype_val))
      exact ENNReal.continuous_ofReal.comp_lowerSemicontinuous ((hlsc ω).comp hc)
        (fun _ _ h => ENNReal.ofReal_le_ofReal h)
  have heq : (fun ω => pathLength (D ω) p) = fun ω => ⨆ n : ℕ, (⨆ u : T, fun ω =>
      ∑ i ∈ Finset.range n, ENNReal.ofReal (D ω (p.extend (u.1 (i + 1))) (p.extend (u.1 i)))) ω := by
    funext ω
    simp only [iSup_apply]
    exact iSup_prod
  rw [heq]
  exact Measurable.iSup fun n => key n

/-- For a pointwise measurable family of distance functions that are lower semicontinuous almost
surely, the length of a fixed path is almost everywhere measurable. -/
theorem aemeasurable_pathLength_of_ae_lowerSemicontinuous
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hlsc : ∀ᵐ ω ∂P, LowerSemicontinuous fun q : ℂ × ℂ => D ω q.1 q.2)
    {x y : ℂ} (p : Path x y) : AEMeasurable (fun ω => pathLength (D ω) p) P := by
  classical
  set N := toMeasurable P {ω | ¬ LowerSemicontinuous fun q : ℂ × ℂ => D ω q.1 q.2} with hNdef
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : P N = 0 := by
    rw [hNdef, measure_toMeasurable]
    exact ae_iff.1 hlsc
  let D' : Ω → ℂ → ℂ → ℝ := fun ω u v => if ω ∈ N then dist u v else D ω u v
  have hD' : ∀ u v, Measurable fun ω => D' ω u v := fun u v =>
    Measurable.ite hN measurable_const (hD u v)
  have hlsc' : ∀ ω, LowerSemicontinuous fun q : ℂ × ℂ => D' ω q.1 q.2 := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [D', hω, ↓reduceIte]
      exact (continuous_fst.dist continuous_snd).lowerSemicontinuous
    · simp only [D', hω, ↓reduceIte]
      by_contra h
      exact hω (subset_toMeasurable _ _ h)
  have hgood : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using hN0
  refine (measurable_pathLength_of_lowerSemicontinuous hD' hlsc' p).aemeasurable.congr ?_
  filter_upwards [hgood] with ω hω
  simp only [D', hω, ↓reduceIte]

end HarmonicBalls
