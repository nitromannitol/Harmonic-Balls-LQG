import HarmonicBalls.Proofs.GFF.PfefferLscAroundMeasurable

/-! # Open-infimum reconstruction for lower semicontinuous distances

A nonnegative lower semicontinuous function is determined by its infima on a
countable topological basis. This applies to the distance functions of weak
metrics without requiring Euclidean continuity.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- The value of a lower semicontinuous function is recovered from its infima
on basis neighborhoods. -/
theorem ofReal_eq_iSup_basis_inf {X : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] {f : X → ℝ} (hf : LowerSemicontinuous f) (x : X) :
    ENNReal.ofReal (f x) = ⨆ U : TopologicalSpace.countableBasis X,
      ⨆ _ : x ∈ U.1, sInf (ENNReal.ofReal ∘ f '' U.1) := by
  classical
  let g : X → ℝ≥0∞ := ENNReal.ofReal ∘ f
  have hg : LowerSemicontinuous g :=
    ENNReal.continuous_ofReal.comp_lowerSemicontinuous hf
      (fun _ _ h => ENNReal.ofReal_le_ofReal h)
  change g x = ⨆ U : TopologicalSpace.countableBasis X,
      ⨆ _ : x ∈ U.1, sInf (g '' U.1)
  apply le_antisymm
  · apply le_of_forall_lt
    intro c hc
    obtain ⟨d, hcd, hd⟩ := exists_between hc
    have ho : IsOpen {y | d < g y} := hg.isOpen_preimage d
    obtain ⟨U, hU, hxU, hsub⟩ :=
      (TopologicalSpace.isBasis_countableBasis X).exists_subset_of_mem_open hd ho
    have hle : d ≤ sInf (g '' U) := by
      apply le_sInf
      rintro _ ⟨y, hy, rfl⟩
      exact le_of_lt (hsub hy)
    calc
      c < d := hcd
      _ ≤ sInf (g '' U) := hle
      _ ≤ ⨆ _ : x ∈ U, sInf (g '' U) := le_iSup (fun _ : x ∈ U => sInf (g '' U)) hxU
      _ ≤ ⨆ V : TopologicalSpace.countableBasis X, ⨆ _ : x ∈ V.1, sInf (g '' V.1) :=
        le_iSup (fun V : TopologicalSpace.countableBasis X =>
          ⨆ _ : x ∈ V.1, sInf (g '' V.1)) ⟨U, hU⟩
  · apply iSup_le
    intro U
    apply iSup_le
    intro hx
    exact sInf_le ⟨x, hx, rfl⟩

/-- The countably many basis infima determine a lower semicontinuous weak
metric at every pair of points. -/
theorem PfefferIsLscMetric.ofReal_eq_iSup_basis_inf {D : ℂ → ℂ → ℝ}
    (hD : PfefferIsLscMetric D) (x y : ℂ) :
    ENNReal.ofReal (D x y) = ⨆ U : TopologicalSpace.countableBasis (ℂ × ℂ),
      ⨆ _ : (x, y) ∈ U.1, sInf ((fun p : ℂ × ℂ => ENNReal.ofReal (D p.1 p.2)) '' U.1) :=
  HarmonicBalls.ofReal_eq_iSup_basis_inf hD.2.2.2.2.2 (x, y)

/-- Two lower semicontinuous weak metrics agree if their infima agree on
each set in a countable basis of the pair space. -/
theorem PfefferIsLscMetric.eq_of_basis_inf_eq {D E : ℂ → ℂ → ℝ}
    (hD : PfefferIsLscMetric D) (hE : PfefferIsLscMetric E)
    (h : ∀ U : TopologicalSpace.countableBasis (ℂ × ℂ),
      sInf ((fun p : ℂ × ℂ => ENNReal.ofReal (D p.1 p.2)) '' U.1) =
      sInf ((fun p : ℂ × ℂ => ENNReal.ofReal (E p.1 p.2)) '' U.1)) : D = E := by
  funext x y
  have he : ENNReal.ofReal (D x y) = ENNReal.ofReal (E x y) := by
    rw [hD.ofReal_eq_iSup_basis_inf x y, hE.ofReal_eq_iSup_basis_inf x y]
    simp only [h]
  have ht := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (hD.2.1 x y),
    ENNReal.toReal_ofReal (hE.2.1 x y)] using ht


/-- Measurable basis infima give joint evaluation of a nonnegative lower
semicontinuous family on the full plane-pair space. -/
theorem measurable_lscMetric_of_basis_inf {Ω : Type*} [MeasurableSpace Ω]
    {D : Ω → ℂ → ℂ → ℝ} (hD : ∀ ω, PfefferIsLscMetric (D ω))
    (hcoord : ∀ U : TopologicalSpace.countableBasis (ℂ × ℂ),
      Measurable fun ω => sInf (Set.image (fun p : ℂ × ℂ =>
        ENNReal.ofReal (D ω p.1 p.2)) U.1)) :
    Measurable fun q : Ω × (ℂ × ℂ) => D q.1 q.2.1 q.2.2 := by
  classical
  let : Countable (TopologicalSpace.countableBasis (ℂ × ℂ)) :=
    (TopologicalSpace.countable_countableBasis (ℂ × ℂ)).to_subtype
  have hm : Measurable fun q : Ω × (ℂ × ℂ) => ⨆ U : TopologicalSpace.countableBasis (ℂ × ℂ),
      if q.2 ∈ U.1 then sInf (Set.image (fun p : ℂ × ℂ =>
        ENNReal.ofReal (D q.1 p.1 p.2)) U.1) else 0 := by
    refine Measurable.iSup fun U => Measurable.ite ?_ ((hcoord U).comp measurable_fst) measurable_const
    exact (TopologicalSpace.isOpen_of_mem_countableBasis U.2).measurableSet.preimage measurable_snd
  have heq : (fun q : Ω × (ℂ × ℂ) => ENNReal.ofReal (D q.1 q.2.1 q.2.2)) =
      fun q => ⨆ U : TopologicalSpace.countableBasis (ℂ × ℂ),
        if q.2 ∈ U.1 then sInf (Set.image (fun p : ℂ × ℂ =>
          ENNReal.ofReal (D q.1 p.1 p.2)) U.1) else 0 := by
    funext q
    rw [(hD q.1).ofReal_eq_iSup_basis_inf q.2.1 q.2.2]
    apply iSup_congr
    intro U
    by_cases h : q.2 ∈ U.1 <;> simp [h]
  have hm2 : Measurable (fun q : Ω × (ℂ × ℂ) =>
      ENNReal.ofReal (D q.1 q.2.1 q.2.2)) := heq ▸ hm
  have hreal := hm2.ennreal_toReal
  simpa only [ENNReal.toReal_ofReal ((hD _).2.1 _ _)] using hreal

end HarmonicBalls
