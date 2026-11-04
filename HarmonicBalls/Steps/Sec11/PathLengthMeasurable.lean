import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-! # Measurability of the length of a fixed path -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- For a pointwise measurable family of continuous distance functions, the
length of a fixed path is measurable. -/
theorem measurable_pathLength_of_continuous
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hcont : ∀ ω, Continuous fun p : ℂ × ℂ => D ω p.1 p.2)
    {x y : ℂ} (p : Path x y) : Measurable fun ω => pathLength (D ω) p := by
  let T := {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1}
  change Measurable (fun ω => ⨆ q : ℕ × T,
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D ω (p.extend (q.2.1 (i + 1))) (p.extend (q.2.1 i))))
  simp_rw [iSup_prod]
  apply Measurable.iSup (ι := ℕ)
  intro n
  let : TopologicalSpace T := TopologicalSpace.induced Subtype.val inferInstance
  let : SecondCountableTopology T := TopologicalSpace.secondCountableTopology_induced T (ℕ → ℝ) Subtype.val
  have hf : Measurable (⨆ u : T, fun ω =>
      ∑ i ∈ Finset.range n, ENNReal.ofReal (D ω (p.extend (u.1 (i + 1))) (p.extend (u.1 i)))) := by
    apply measurable_iSup_of_lowerSemicontinuous
    · intro u
      exact Finset.measurable_sum _ (fun i _ => (hD _ _).ennreal_ofReal)
    · intro ω
      apply Continuous.lowerSemicontinuous
      apply continuous_finsetSum
      intro i hi
      apply ENNReal.continuous_ofReal.comp
      exact (hcont ω).comp
        ((p.continuous_extend.comp ((continuous_apply (i + 1)).comp continuous_subtype_val)).prodMk
          (p.continuous_extend.comp ((continuous_apply i).comp continuous_subtype_val)))
  convert hf using 1
  ext ω
  simp only [iSup_apply]

/-- Almost-sure length-metric regularity gives almost-everywhere measurability
of the length of a fixed path. -/
theorem aemeasurable_pathLength_of_ae_lengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {x y : ℂ} (p : Path x y) : AEMeasurable (fun ω => pathLength (D ω) p) P := by
  classical
  let H : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have hH : NullMeasurableSet H P := by
    apply (nullMeasurableSet_univ (μ := P)).congr
    filter_upwards [hmetric] with ω hω
    simp only [mem_univ, H, mem_ofPred_eq, hω]
  obtain ⟨G, hsub, hG, hGeq⟩ := hH.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hGeq, hmetric] with ω heq hω
    exact Eq.mpr heq hω
  let D' : Ω → ℂ → ℂ → ℝ := fun ω u v => if ω ∈ G then D ω u v else dist u v
  have hD' : ∀ u v, Measurable fun ω => D' ω u v := by
    intro u v
    exact Measurable.ite hG (hD u v) measurable_const
  have hcont : ∀ ω, Continuous fun q : ℂ × ℂ => D' ω q.1 q.2 := by
    intro ω
    by_cases hω : ω ∈ G
    · simpa only [D', hω, ↓reduceIte] using (hsub hω).continuous_pair
    · simpa only [D', hω, ↓reduceIte] using (continuous_fst.dist continuous_snd :
        Continuous fun q : ℂ × ℂ => dist q.1 q.2)
  have hm := (measurable_pathLength_of_continuous hD' hcont p).aemeasurable (μ := P)
  apply hm.congr
  filter_upwards [hGae] with ω hω
  simp only [D', hω, ↓reduceIte]

end HarmonicBalls
