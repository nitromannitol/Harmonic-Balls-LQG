import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.Phase2.GFFJointLaw

/-!
# Cameron-Martin transfer of the shifted closed event

Target: `cameronMartinEventTransfer_derived : CameronMartinEventTransferFrozen.{u}` (`FirstPass/Frozen/S11c.lean:149`).

Route: the Cameron-Martin
measure `P'` (equivalent to `P`) under which the shifted sample `(hC + f, hcirc + Av f)` has the law of
`(hC, hcirc)` under `P` (`GFFJointLaw.cameronMartin_profileLaw_map_eq`), and the Weyl identities transfer the
shifted observables to the sample.

This file proves the measure-theoretic core of the route and reduces the target to one named representation
statement `EventSampleRepresentation` (a BLOCKED-STEP, see the docstring there). The target itself is NOT derived here.

Steps:
* `transfer_of_law` (abstract Cameron-Martin transfer): proved.
* `cameronMartinEventTransfer_of_representation`: the frozen statement, conditional on
  `EventSampleRepresentation` and `CameronMartinGFFReweighting`.
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

universe u

namespace CMEventTransfer

/-- The codomain of `GFFJointLaw.jointSample`: pairings with test functions and circle averages of positive radius. -/
abbrev Sample := ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) × ({p : ℝ × ℂ // 0 < p.1} → ℝ)

/-- **Step R1 (abstract Cameron-Martin transfer).** If `P ≪ P'`, the samples `Y` (under `P`) and `Y'` (under `P'`)
have the same law, and the events `A` and `As` are a.s. the preimages of one measurable set `E`, then positivity of
`As` under `P` gives positivity of `A` under `P`. -/
theorem transfer_of_law {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P P' : Measure Ω) (hac : P ≪ P') (Y Y' : Ω → X) (hY : Measurable Y) (hY' : Measurable Y')
    (hlaw : P'.map Y' = P.map Y) (E : Set X) (hE : MeasurableSet E) (A As : Set Ω)
    (hA : A =ᵐ[P] Y ⁻¹' E) (hAs : As =ᵐ[P] Y' ⁻¹' E) (hpos : 0 < P As) : 0 < P A := by
  have key : P' (Y' ⁻¹' E) = P (Y ⁻¹' E) := by
    rw [← Measure.map_apply hY' hE, hlaw, Measure.map_apply hY hE]
  have h1 : 0 < P (Y' ⁻¹' E) := by
    rwa [← measure_congr hAs]
  have h2 : 0 < P' (Y' ⁻¹' E) := by
    refine pos_iff_ne_zero.2 fun h0 => ?_
    exact (pos_iff_ne_zero.1 h1) (hac h0)
  rw [measure_congr hA, ← key]
  exact h2

/-- **BLOCKED-STEP R4 (named, NOT derived).** The unshifted and the Cameron-Martin shifted closed events are, almost
surely, preimages of one measurable set `E` of the joint sample space, for every admissible shift `f`.
Missing ingredient: a jointly measurable version of the canonical event functional
`(μ, D) ↦ (sup_{u,v ∈ S₂} internalMetric D S₂ u v ≤ c ∧ C ≤ μ S₁)` on `Sample`, valid for the field and for its
Weyl-shifted field. `AEMeasurable` of the observables (the frozen hypotheses) does not supply it: the shift law
transfers only sets that are measurable in the sample. The Weyl identities (`LQGMeasureWeylScaling`,
`LQGMetricFieldAxioms` III together with `IsLQGMetric.satisfiesLQGMetricAxioms`) identify the shifted observables
with the observables of the shifted sample, but the single set `E` is what is not available in Lean. -/
def EventSampleRepresentation : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (S₁ S₂ : Set ℂ) (c C : ℝ≥0∞),
    0 < γ → γ < 2 → α₀ < lqgQ γ → IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ ξ α₀ hC D → IsClosedDyadicSquare S₁ → IsClosedDyadicSquare S₂ →
    ∃ E : Set Sample, MeasurableSet E ∧
      ∀ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
        (∀ᵐ ω ∂P, ((⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (D ω) S₂ u v) ≤ c ∧ C ≤ μ ω S₁) ↔
            GFFJointLaw.jointSample hC hcirc ω ∈ E) ∧
        (∀ᵐ ω ∂P, ((⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ c ∧
            C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁) ↔
          GFFJointLaw.jointSample (fun ω => addFunPairing (hC ω) f)
            (fun ω r z => hcirc ω r z + Real.circleAverage f z r) ω ∈ E)

/-- **Step R2.** The frozen Cameron-Martin event transfer, conditional on the named representation
`EventSampleRepresentation` and on the Cameron-Martin reweighting `CameronMartinGFFReweighting`
(`FirstPass/Frozen/S11aj.lean:33`). This is a reduction, not the derived target. -/
theorem cameronMartinEventTransfer_of_representation
    (hRep : EventSampleRepresentation.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u}) :
    CameronMartinEventTransferFrozen.{u} := by
  intro γ α₀ ξ f hγ0 hγ2 hα hf hfc hf0 Ω _ P hC hcirc μ D S₁ S₂ c C hW hμ hD hS₁ hS₂ _ _ _ hPos
  have : IsProbabilityMeasure P := hW.isGaussianProcess.isProbabilityMeasure
  obtain ⟨E, hE, hrep⟩ := hRep γ ξ α₀ Ω P hC hcirc μ D S₁ S₂ c C hγ0 hγ2 hα hW hμ hD hS₁ hS₂
  have hf0' : Real.circleAverage f 0 1 = 0 := by
    have h := Real.circleAverage_congr_sphere (c := (0 : ℂ)) (R := (1 : ℝ)) (f₁ := f)
      (f₂ := 0) (fun z hz => hf0 z (by simpa using hz))
    rw [h]
    simp [Real.circleAverage]
  obtain ⟨P', -, hac', hlaw⟩ :=
    GFFJointLaw.cameronMartin_profileLaw_map_eq hCMRew P hC hcirc hW f hf hfc hf0'
  have hY : Measurable (GFFJointLaw.jointSample hC hcirc) := by
    rw [GFFJointLaw.jointSample_eq_pairOfFamily]
    exact GFFJointLaw.measurable_pairOfFamily.comp (GFFJointLaw.measurable_obsFamily_map hW)
  have hY' : Measurable (fun ω => GFFJointLaw.jointSample (fun ω => addFunPairing (hC ω) f)
      (fun ω r z => hcirc ω r z + Real.circleAverage f z r) ω) := by
    unfold GFFJointLaw.jointSample
    refine Measurable.prodMk (Measurable.of_eval fun φ => ?_) (Measurable.of_eval fun p => ?_)
    · exact (hW.measurable_pairing φ.1 φ.2).add_const _
    · exact (hW.measurable_circle p.1.1 p.1.2 p.2).add_const _
  refine transfer_of_law P P' hac' (GFFJointLaw.jointSample hC hcirc)
    (fun ω => (fun φ : {φ : ℂ → ℝ // IsTestFunction Set.univ φ} => addFunPairing (hC ω) f φ.1,
      fun p : {p : ℝ × ℂ // 0 < p.1} => hcirc ω p.1.1 p.1.2 + Real.circleAverage f p.1.2 p.1.1))
    hY hY' hlaw E hE _ _ ?_ ?_ hPos
  · exact (hrep f hf hfc hf0).1.mono fun ω hω => propext hω
  · exact (hrep f hf hfc hf0).2.mono fun ω hω => propext hω

end CMEventTransfer

end HarmonicBalls
