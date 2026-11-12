import HarmonicBalls.FirstPass.Phase2.Step8RootedModelCert
import HarmonicBalls.FirstPass.Phase2.LocalDecoderCommonDerived
import HarmonicBalls.FirstPass.Phase2.SquarePositiveHolds
import HarmonicBalls.FirstPass.Phase2.NonatomicHolds
import HarmonicBalls.FirstPass.Phase2.CampbellDerivedWrappers
import HarmonicBalls.FirstPass.S11i.InsertionZeroUnitE

/-!
# Step 8 of Lemma 11.13: insertion-zero unit frequency from the seed of Lemma 11.12

For a coding event `E` of the Lemma 11.12 construction, `InsertionZeroUnitStmt γ E` (the unit-ball frequency of the
certificate events is the common probability `q` of `E`, in every whole-plane insertion-zero model) follows from:

* the seed `hEq` of Lemma 11.12: in every insertion-`γ` model, almost surely `E` holds for the local field on `B(0,7)`
  if and only if the certificate event at radius `1` about `0` holds;
* the local metric replacement `hR` (clauses (18) and (20)), the continuity of the rooted physical metric at the
  insertion point `hfr`, and the field axioms of LQG metrics `hAx`.

The local measure kernel, the positivity of the LQG measure of squares, the non-atomicity of the LQG measure and the
marked whole-plane Lemma A.10 of Duplantier-Miller-Sheffield are supplied by their proofs. No canonical decoder and no
uniqueness of the LQG metric enter.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassPhase2Step8InsertionZeroUnitSeed

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassPhase2Step8RootedModelCert
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iInsertionZeroUnitE

/-- **Insertion-zero unit frequency from the seed of Lemma 11.12.** For a buffered pinch geometry and a measurable
coding event `E` satisfying the seed `hEq`, `E` has the insertion-zero unit frequency `InsertionZeroUnitStmt.{0}`.
The local measure kernel, the positivity of the LQG measure of squares, its non-atomicity and the marked whole-plane
Lemma A.10 of Duplantier-Miller-Sheffield are supplied by their proofs; the remaining inputs are `hR`, `hfr` and
`hAx`. -/
theorem insertionZeroUnit_of_seed {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0}) (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)) :
    InsertionZeroUnitStmt.{0} γ E U V W T Q' Q δ M :=
  have hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂ :=
    fun c₁ c₂ r₁ r₂ => LocalDecoderCommon.localMeasureKernelStmt_derived γ c₁ c₂ r₁ r₂
  insertionZeroUnit_of_href hγ0 hγ2 hgeo hK hR hfr lqgMeasureSquarePositiveFrozen_holds.{0}
    (fun Ω _ P hC hcirc => lqgMeasureNonatomic_holds.{0} Ω P γ 0 hC hcirc)
    (fun Ω _ P hC hcirc μ => dmsLemmaA10WholePlaneMarkedSub_forall.{0} Ω P γ hC hcirc μ)
    (hHref_of_seed hγ0 hγ2 hgeo hK hR hfr hAx hE hEq)

end HarmonicBalls.FirstPassPhase2Step8InsertionZeroUnitSeed
