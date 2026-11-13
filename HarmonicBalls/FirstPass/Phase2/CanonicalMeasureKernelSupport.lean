import HarmonicBalls.FirstPass.Phase2.CanonicalMeasureKernel
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived

/-!
# Full support of the canonical measure kernel

`exists_canonicalMeasureKernel` gives an s-finite kernel `K` from the canonical space to `ℂ` such that, for every
whole-plane GFF model and every LQG measure `μ` of the field `h^ℂ - α₀ log|·|`, almost surely
`μ ω = a • K (alphaCanon α₀ hC ω)` with `a > 0`. This file adds the support clause.

* `fullSupportSet κ` is the set of canonical fields `ℓ` at which `κ ℓ` charges every nonempty open set. By a countable
  basis of `ℂ` it is a countable intersection of the measurable sets `{ℓ | 0 < κ ℓ s}` (`measurableSet_fullSupportSet`),
  and on it the support of `κ ℓ` is the whole plane (`support_eq_univ_of_mem_fullSupportSet`).
* Every whole-plane GFF model carries an LQG measure (`lqgMeasureExistence_derived`), which has full support almost surely
  (`lqgMeasureFullSupportStmt_holds`); since it is almost surely a positive multiple of `K` at the canonical field, the
  canonical field lies almost surely in `fullSupportSet K` (`exists_canonicalMeasureKernel_fullSupport`).
-/

noncomputable section

universe u

namespace HarmonicBalls.CanonicalMeasureKernel

open MeasureTheory Set ProbabilityTheory TopologicalSpace
open scoped ENNReal

/-- The canonical fields at which the kernel charges every nonempty open subset of the plane. -/
def fullSupportSet (κ : Kernel S11n.CanonSpace ℂ) : Set S11n.CanonSpace :=
  {ℓ | ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < κ ℓ U}

/-- `fullSupportSet κ` is measurable: it is the intersection, over a countable basis of nonempty open sets of `ℂ`, of
the measurable sets `{ℓ | 0 < κ ℓ s}`. -/
theorem measurableSet_fullSupportSet (κ : Kernel S11n.CanonSpace ℂ) : MeasurableSet (fullSupportSet κ) := by
  obtain ⟨b, hbc, hb0, hb⟩ := exists_countable_basis ℂ
  have heq : fullSupportSet κ = ⋂ s ∈ b, {ℓ | 0 < κ ℓ s} := by
    ext ℓ
    simp only [fullSupportSet, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h s hs
      exact h s (hb.isOpen hs) (nonempty_iff_ne_empty.2 fun he => hb0 (he ▸ hs))
    · intro h U hU ⟨x, hx⟩
      obtain ⟨s, hs, hxs, hsU⟩ := hb.exists_subset_of_mem_open hx hU
      exact (h s hs).trans_le (measure_mono hsU)
  rw [heq]
  exact MeasurableSet.biInter hbc fun s hs =>
    measurableSet_lt measurable_const (κ.measurable_coe (hb.isOpen hs).measurableSet)

/-- On `fullSupportSet κ` the support of the decoded measure is the whole plane. -/
theorem support_eq_univ_of_mem_fullSupportSet {κ : Kernel S11n.CanonSpace ℂ} {ℓ : S11n.CanonSpace}
    (h : ℓ ∈ fullSupportSet κ) : (κ ℓ).support = univ := by
  have : (κ ℓ).IsOpenPosMeasure := ⟨fun U hU hne => (h U hU hne).ne'⟩
  exact Measure.support_eq_univ

/-- If almost surely the LQG measure `μ ω` is a positive multiple of `K` at the canonical field, then almost surely the
canonical field lies in `fullSupportSet K`: the LQG measure has full support almost surely. -/
theorem ae_alphaCanon_mem_fullSupportSet {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (K : Kernel S11n.CanonSpace ℂ) {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hK : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ ω = ENNReal.ofReal a • K (alphaCanon α₀ hC ω)) :
    ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ fullSupportSet K := by
  filter_upwards [hK, lqgMeasureFullSupportStmt_holds γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hG hμ]
    with ω hω hfull U hU hne
  obtain ⟨a, -, he⟩ := hω
  have hpos := hfull U hU hne
  rw [he, Measure.smul_apply, smul_eq_mul] at hpos
  refine pos_iff_ne_zero.2 fun h0 => hpos.ne' ?_
  rw [h0, mul_zero]

/-- The canonical measure kernel with its support clause (the measure half of hCanonX lemma B8), with no hypotheses:
an s-finite kernel `K`, finite on compact sets, which almost surely decodes the LQG measure of every whole-plane GFF model
up to a positive factor, and whose measurable full-support set contains the canonical field of every whole-plane GFF
model almost surely. -/
theorem exists_canonicalMeasureKernel_fullSupport (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) :
    ∃ K : Kernel S11n.CanonSpace ℂ, IsSFiniteKernel K ∧ (∀ ℓ, IsFiniteMeasureOnCompacts (K ℓ)) ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ ω = ENNReal.ofReal a • K (alphaCanon α₀ hC ω)) ∧
      MeasurableSet (fullSupportSet K) ∧ (∀ ℓ ∈ fullSupportSet K, (K ℓ).support = univ) ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ fullSupportSet K := by
  obtain ⟨K, hKs, hKc, hK⟩ := exists_canonicalMeasureKernel.{u} γ α₀ hγ0 hγ2 hα
  refine ⟨K, hKs, hKc, hK, measurableSet_fullSupportSet K, fun ℓ hℓ => support_eq_univ_of_mem_fullSupportSet hℓ, ?_⟩
  intro Ω _ P hC hcirc hG
  obtain ⟨μ, hμ⟩ := lqgMeasureExistence_derived P γ α₀ hC hcirc hG hγ0 hγ2 hα
  exact ae_alphaCanon_mem_fullSupportSet hγ0 hγ2 hα K hG hμ (hK Ω P hC hcirc μ hG hμ)

end HarmonicBalls.CanonicalMeasureKernel

end
