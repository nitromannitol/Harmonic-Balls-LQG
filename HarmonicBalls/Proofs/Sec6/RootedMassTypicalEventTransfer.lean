import HarmonicBalls.Proofs.Sec6.RootedNearbyAnnulusCounts

/-! # Transfer of mass-typical comparisons to rooted probability

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

/-- A measurable rooted event is bounded by a measurable field event when
its sections are contained in that field event at mass-typical roots. The
sampling kernel may depend on the field but must be normalized and absolutely
continuous with respect to the random mass measure. -/
theorem compProd_measure_le_of_ae_mass_event_implication
    {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    (P : Measure Ω) [SFinite P] (μ : Ω → Measure Z)
    (κ : Kernel Ω Z) [IsSFiniteKernel κ]
    (hκ : ∀ᵐ ω ∂P, κ ω univ = 1)
    (hac : ∀ᵐ ω ∂P, κ ω ≪ μ ω)
    {E : Set (Ω × Z)} (hE : MeasurableSet E)
    {F : Set Ω} (hF : MeasurableSet F)
    (himp : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), (ω, z) ∈ E → ω ∈ F) :
    (P ⊗ₘ κ) E ≤ P F := by
  have hmeas : MeasurableSet {p : Ω × Z | p ∉ E ∨ p.1 ∈ F} :=
    hE.compl.union (hF.preimage measurable_fst)
  have hae : ∀ᵐ p ∂(P ⊗ₘ κ), p ∉ E ∨ p.1 ∈ F := by
    apply Measure.ae_compProd_of_ae_ae hmeas
    filter_upwards [hac, himp] with ω hω hi
    filter_upwards [hω.ae_le hi] with z hz
    by_cases h : (ω, z) ∈ E
    · exact Or.inr (hz h)
    · exact Or.inl h
  have hle : (P ⊗ₘ κ) E ≤ (P ⊗ₘ κ) (Prod.fst ⁻¹' F) := by
    apply measure_mono_ae
    filter_upwards [hae] with p hp hpE
    exact hp.resolve_left (not_not_intro hpE)
  have hp := measurePreserving_fst_compProd_of_ae_normalized P κ hκ
  exact hle.trans_eq (hp.measure_preimage hF.nullMeasurableSet)

/-- The same bound applies to normalized weighted LQG-mass sampling. -/
theorem weightedRestriction_compProd_measure_le_of_ae_mass_event_implication
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hmass : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ 0 ∧
      ((μ ω).withDensity w) B ≠ ∞)
    {E : Set (Ω × ℂ)} (hE : MeasurableSet E)
    {F : Set Ω} (hF : MeasurableSet F)
    (himp : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), (ω, z) ∈ E → ω ∈ F) :
    (P ⊗ₘ weightedRestrictionKernel P μ hμ B hB w hw) E ≤ P F := by
  apply compProd_measure_le_of_ae_mass_event_implication P μ _ ?_ ?_ hE hF himp
  · filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw, hmass] with ω he hm
    rw [he]
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hm.1 hm.2
  · filter_upwards [ae_weightedRestrictionKernel_eq P μ hμ B hB w hw] with ω he
    rw [he, normalizedRestriction]
    exact Measure.smul_absolutelyContinuous.trans
      (Measure.absolutelyContinuous_restrict.trans (withDensity_absolutelyContinuous _ _))

end HarmonicBalls.Section6
