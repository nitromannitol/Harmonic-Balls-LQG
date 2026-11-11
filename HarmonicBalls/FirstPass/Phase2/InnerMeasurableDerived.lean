import HarmonicBalls.FirstPass.Frozen.S11k
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-! # Inner measurability of the LQG mass and of the internal diameter

Derives the two inner-measurability interfaces of `FirstPass/Frozen/S11k.lean` from literature inputs of
`HarmonicBalls/Proposed/LQG.lean`, with no other hypothesis:

* `lqgMassInnerMeasurable_derived : LQGMassInnerMeasurableFrozen` (Frozen/S11k.lean:66), from `LQGMeasureLocality`
  (Fact 2.1 II, Bou-Rabee-Gwynne arXiv:2208.11795, p. 9): the mass of an open set depends only on the field there.
* `lqgInternalDiamInnerMeasurable_derived : LQGInternalDiamInnerMeasurableFrozen` (Frozen/S11k.lean:89), from
  `LQGMetricFieldAxioms` (Fact 2.2 I-II, p. 10; Gwynne-Miller arXiv:1905.00383, Section 1.2, Axioms I-II): the internal
  metric on `thickening δ A` is a.s. a `σ(h|_O)`-measurable function of the endpoints, the internal diameter is a supremum
  over `A`, and the supremum over `A` is a supremum over a countable dense subset of `A` by the continuity of the
  internal metric on `O × O` (`IsEuclideanLengthMetric.continuousOn_internalMetric_pair`).

The field σ-algebra is monotone in the open set (`fieldSigmaAlgebra_mono_of_subset`). -/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

universe u

/-- The σ-algebra of the field restricted to a smaller set is contained in the one of a larger set:
`σ(h|_U) ≤ σ(h|_O)` for `U ⊆ O`, since a test function supported in `U` is supported in `O`. -/
theorem fieldSigmaAlgebra_mono_of_subset {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) {U O : Set ℂ}
    (hUO : U ⊆ O) : fieldSigmaAlgebra α₀ hC U ≤ fieldSigmaAlgebra α₀ hC O := by
  unfold fieldSigmaAlgebra
  refine iSup₂_le fun φ hφ => ?_
  obtain ⟨h1, h2, h3⟩ := hφ
  exact le_iSup₂_of_le φ (show IsTestFunction O φ from ⟨h1, h2, h3.trans hUO⟩) le_rfl

/-- Inner measurability of the LQG mass, from the locality input `LQGMeasureLocality` (Fact 2.1 II) for every
probability space: the mass of `U`, with `closure U ⊆ O`, is a.s. equal to a `σ(h|_O)`-measurable variable, since it is
`σ(h|_U)`-measurable and `σ(h|_U) ≤ σ(h|_O)`. -/
theorem lqgMassInnerMeasurable_derived
    (hLoc : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality.{u} P γ α₀ hC hcirc) :
    LQGMassInnerMeasurableFrozen.{u} := by
  intro γ α₀ Ω _ P _ hC hcirc μ hW h0 h1 h2 hμ O U hO hU _ hcl
  obtain ⟨Y, hYm, hYae⟩ := hLoc Ω P γ α₀ hC hcirc hW h0 h1 h2 μ hμ U hU
  refine ⟨Y, hYm.mono (fieldSigmaAlgebra_mono_of_subset α₀ hC (subset_closure.trans hcl)) le_rfl, hYae⟩

/-- Reduction of a supremum over a compact set to a countable dense subset: if `F` is continuous on `A × A`
(`A` compact, `Q ⊆ A` countable and dense in `A`), then `sup_{x ∈ A} sup_{y ∈ A} F x y = sup_{x ∈ Q} sup_{y ∈ Q} F x y`.
Proof: the set where `F ≤ b` (`b` the right-hand side) is relatively closed in `A × A` and contains `Q × Q`, hence
`A × A`. -/
theorem iSup_iSup_compact_eq_countable {F : ℂ → ℂ → ℝ≥0∞} {A Q : Set ℂ} (hA : IsCompact A)
    (hQA : Q ⊆ A) (hAQ : A ⊆ closure Q)
    (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (A ×ˢ A)) :
    (⨆ x ∈ A, ⨆ y ∈ A, F x y) = ⨆ x : Q, ⨆ y : Q, F x y := by
  apply le_antisymm
  · have hclosed : IsClosed ((A ×ˢ A) ∩ (fun p : ℂ × ℂ => F p.1 p.2) ⁻¹' Iic (⨆ x : Q, ⨆ y : Q, F x y)) :=
      hF.preimage_isClosed_of_isClosed (hA.isClosed.prod hA.isClosed) isClosed_Iic
    have hQQ : Q ×ˢ Q ⊆
        (A ×ˢ A) ∩ (fun p : ℂ × ℂ => F p.1 p.2) ⁻¹' Iic (⨆ x : Q, ⨆ y : Q, F x y) := by
      rintro ⟨x, y⟩ ⟨hx, hy⟩
      refine ⟨⟨hQA hx, hQA hy⟩, ?_⟩
      show F x y ≤ ⨆ x' : Q, ⨆ y' : Q, F x' y'
      exact le_iSup_of_le (⟨x, hx⟩ : Q) (le_iSup_of_le (⟨y, hy⟩ : Q) le_rfl)
    have hsub : A ×ˢ A ⊆ closure (Q ×ˢ Q) := by
      rw [closure_prod_eq]
      exact prod_mono hAQ hAQ
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => ?_
    have hmem : (x, y) ∈ closure (Q ×ˢ Q) := hsub (show (x, y) ∈ A ×ˢ A from ⟨hx, hy⟩)
    exact (closure_minimal hQQ hclosed hmem).2
  · refine iSup_le fun x => iSup_le fun y => ?_
    exact le_iSup₂_of_le (x : ℂ) (hQA x.2) (le_iSup₂_of_le (y : ℂ) (hQA y.2) le_rfl)

/-- Inner measurability of the internal diameter of a compact set `A` for an LQG metric `D` of the field
(`IsLQGMetricOfField`), with `O = thickening δ A`. From `LQGMetricFieldAxioms` (Fact 2.2 I-II): the internal metric
`D(·, ·; O)` is a.s. equal to a family `G` of `σ(h|_O)`-measurable functions, and `D` is a.s. a Euclidean length metric,
whose internal metric is continuous on `O × O`. Hence `internalDiam D δ A` is a.s. the supremum of `G` over a countable
dense subset of `A`, which is `σ(h|_O)`-measurable. -/
theorem lqgInternalDiamInnerMeasurable_derived
    (hFA : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    LQGInternalDiamInnerMeasurableFrozen.{u} := by
  intro γ ξ α₀ Ω _ P _ hC hcirc D hW h0 h1 h2 hD δ A hδ hA
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  obtain ⟨hI, hII, -, -⟩ := hFA γ ξ α₀ Ω P hC hcirc hW h0 h1 h2 𝔇 h𝔇
  have hO : IsOpen (thickening δ A) := isOpen_thickening
  have hAO : A ⊆ thickening δ A := self_subset_thickening hδ A
  obtain ⟨G, hGm, hGae⟩ := hII (thickening δ A) hO
  obtain ⟨Q, hQc, hQA, hAQ⟩ := TopologicalSpace.exists_countable_dense_subset A
  have : Countable Q := hQc.to_subtype
  refine ⟨fun ω => ⨆ x : Q, ⨆ y : Q, G ω x y, ?_, ?_⟩
  · exact Measurable.iSup fun x => Measurable.iSup fun y => hGm x y
  · filter_upwards [hI, hGae, hDae] with ω hIω hGω hDω
    have hDeq : ∀ u v, D ω u v = (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal := by
      intro u v
      obtain ⟨h0', h1'⟩ := hDω u v
      rw [← h1', ENNReal.toReal_ofReal h0']
    have hfun : D ω = fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v).toReal :=
      funext fun u => funext fun v => hDeq u v
    have hnn : ∀ x y, 0 ≤ D ω x y := fun x y => by rw [hDeq x y]; exact ENNReal.toReal_nonneg
    have hIE : IsEuclideanLengthMetric (D ω) := by
      rw [hfun]
      exact hIω.2
    have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric (D ω) (thickening δ A) p.1 p.2) (A ×ˢ A) :=
      (hIE.continuousOn_internalMetric_pair hnn hO).mono (prod_mono hAO hAO)
    have hred := iSup_iSup_compact_eq_countable (F := internalMetric (D ω) (thickening δ A)) hA hQA hAQ hcont
    rw [internalDiam, hred, hfun]
    exact iSup_congr fun x => iSup_congr fun y => hGω x.1 (hAO (hQA x.2)) y.1 (hAO (hQA y.2))

end HarmonicBalls
