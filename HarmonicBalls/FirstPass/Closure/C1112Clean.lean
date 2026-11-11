import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.Closure.Sec11

/-!
# Lemma 11.12 (corrected) without the redundant component clause

`CorrectedLemma11_12Stmt` (`FirstPass/S11i/Faithful.lean:62`) carries the premise
`insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ₀` (corrected paper lines 3180-3200). This premise
follows from the buffered geometry `IsBufferedPinchGeometry U V W T Q' Q δ₀` alone, by
`FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom` (`FirstPass/S11ap.lean:93`), so it is redundant.

This file states the lemma without that premise (`CorrectedLemma11_12CleanStmt`). Its body is the body of
`CorrectedLemma11_12Stmt` with the premise line removed, and nothing else is changed. The two statements are equivalent:
`correctedLemma11_12Clean_of_stmt` gives the clean form from the original, and `correctedLemma11_12_of_clean` gives the
original back. The clean form of `closure_11_12` is `closure_11_12_clean`, with the same binders as `closure_11_12`.
-/

universe u

namespace HarmonicBalls.Closure

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- **Lemma 11.12 (corrected), clean form.** The statement `CorrectedLemma11_12Stmt` without its premise
`insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ₀`, which is derived from the buffered geometry
(`FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom`). -/
def CorrectedLemma11_12CleanStmt : Prop :=
  ∀ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ →
  ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ M : ℝ, 0 < M →
  ∃ E : Set (ModConstTestPairings (ball (0 : ℂ) 7)), MeasurableSet E ∧
  ∀ α : ℝ, α < lqgQ γ →
  ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → IsLQGMetricOfField P γ ξ α hC D →
    MeasurableSet[Section6.fieldSigmaAlgebraModConst α hC (ball (0 : ℂ) 7)]
      {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    0 < P {ω | localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E} ∧
    ∀ᵐ ω ∂P, localModConstField α hC (ball (0 : ℂ) 7) ω ∈ E →
      pinchPointEvent (μ ω) (D ω) U T Q' Q M 1 0

/-- The original statement implies the clean one: the dropped premise is supplied by
`FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom` from the same buffered geometry. -/
theorem correctedLemma11_12Clean_of_stmt (h : CorrectedLemma11_12Stmt.{u}) :
    CorrectedLemma11_12CleanStmt.{u} := by
  unfold CorrectedLemma11_12CleanStmt
  intro U V W T Q' Q δ₀ hgeo
  exact h U V W T Q' Q δ₀ hgeo (FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo)

/-- The clean statement implies the original one (the premise is simply not used). -/
theorem correctedLemma11_12_of_clean (h : CorrectedLemma11_12CleanStmt.{u}) :
    CorrectedLemma11_12Stmt.{u} := by
  unfold CorrectedLemma11_12Stmt
  intro U V W T Q' Q δ₀ hgeo _
  exact h U V W T Q' Q δ₀ hgeo

/-- **Closure of Lemma 11.12, clean form** (`CorrectedLemma11_12CleanStmt`). Same inputs as `closure_11_12`
(`FirstPass/Closure/Sec11.lean:357`); the conclusion is the clean statement, obtained from `closure_11_12` by
`correctedLemma11_12Clean_of_stmt`. -/
theorem closure_11_12_clean
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hLen : LQGMetricLengthUnivFrozen.{u})
    (hN2 : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → 0 < ξ → ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ,
      LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hμW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ α₀ hC hcirc)
    (hLoc : LocalLQGDecoderCommonFrozen.{u})
    (hCanon : LQGCanonicalDecodersExistStmt.{u})
    (hNonat : HarmonicBalls.S11n.MeasureDecoder.LQGMeasureNonatomicAll.{u})
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hmass : LQGMassFunctionalMeasurableFrozen.{u})
    (hCMAbs : CameronMartinGFFMutualAbsCont.{u})
    (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hComp : WeylScalingCompositionFrozen.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u})
    (hShift : LQGMetricContinuousShiftFactI.{u}) (hFD : PlaneDomainMinusConvexCompactPreconnectedFrozen)
    (hDC : DyadicCellDiamSmallFrozen.{u}) (hCMT : CameronMartinEventTransferFrozen.{u})
    (hPos10 : LQGMeasureSquarePositiveFrozen.{u}) (hMassM : LQGMeasureSquareMeasurableFrozen.{u})
    (hSupM : LQGMetricSupMeasurableFrozen.{u}) (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u})
    (hW : WeylInternalClosedFrozen)
    (hM1 : WeylShiftedSupMeasurableFrozen.{u}) (hM2 : WeylShiftedMassMeasurableFrozen.{u}) :
    CorrectedLemma11_12CleanStmt.{u} :=
  correctedLemma11_12Clean_of_stmt
    (closure_11_12 hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG hCC hE hfr hmass hCMAbs hCMRew hComp
      hMf hDiam hMk hholder hShift hFD hDC hCMT hPos10 hMassM hSupM hFin hW hM1 hM2)

end HarmonicBalls.Closure
