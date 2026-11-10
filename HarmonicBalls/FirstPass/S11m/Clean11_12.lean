import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11m.Final11_12

/-!
# Lemma 11.12 in the corrected form, without the component premise (clean statement)

Operator note 07:44 UTC, item (4). Route: `notes/fp-gaps/CHATGPT-hb-11-12-audit-PRO.md`, section 3.2 ("the component clause").
The corrected statement `CorrectedLemma11_12Stmt` (FirstPass/S11i/Faithful.lean:61) carries the component premise
`insert 0 (sphere 0 5) ⊆ pinchOmegaGeom W Q δ₀`. That premise follows from `IsBufferedPinchGeometry` alone by
`FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom` (FirstPass/S11ap.lean:93), so it is redundant.

This module defines the premise-free statement `CorrectedLemma11_12CleanStmt`, proves it equivalent to
`CorrectedLemma11_12Stmt`, and restates `firstPass_11_12_final` (FirstPass/S11m/Final11_12.lean:131) with the clean
conclusion. No existing file is edited.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls.S11m.Clean11_12

universe u

/-- Lemma 11.12 in the corrected form, without the component premise (operator note 07:44 UTC, item (4); audit
`notes/fp-gaps/CHATGPT-hb-11-12-audit-PRO.md`, section 3.2). This is the body of `CorrectedLemma11_12Stmt`
(FirstPass/S11i/Faithful.lean:61) with the single premise `insert (0 : ℂ) (sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ₀`
deleted. Under `IsBufferedPinchGeometry` that premise holds by `FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom`. -/
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

/-- The premise-free statement implies `CorrectedLemma11_12Stmt`: the component premise is ignored. -/
theorem correctedLemma11_12Stmt_of_clean : CorrectedLemma11_12CleanStmt.{u} → CorrectedLemma11_12Stmt.{u} :=
  fun H U V W T Q' Q δ₀ hgeo _ => H U V W T Q' Q δ₀ hgeo

/-- `CorrectedLemma11_12Stmt` implies the premise-free statement: the component premise is supplied by
`FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom` from the buffered geometry. -/
theorem correctedLemma11_12Clean_of_stmt : CorrectedLemma11_12Stmt.{u} → CorrectedLemma11_12CleanStmt.{u} :=
  fun H U V W T Q' Q δ₀ hgeo =>
    H U V W T Q' Q δ₀ hgeo (FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo)

/-- The premise-free statement and `CorrectedLemma11_12Stmt` are equivalent (operator note 07:44 UTC, item (4)). -/
theorem correctedLemma11_12CleanStmt_iff :
    CorrectedLemma11_12CleanStmt.{u} ↔ CorrectedLemma11_12Stmt.{u} :=
  ⟨correctedLemma11_12Stmt_of_clean, correctedLemma11_12Clean_of_stmt⟩

/-- **Lemma 11.12, clean form (corrected lemma 11.12, `[C43]`).** Same hypotheses as `firstPass_11_12_final`
(FirstPass/S11m/Final11_12.lean:131); the conclusion is the premise-free `CorrectedLemma11_12CleanStmt`. The proof is
`firstPass_11_12_final` followed by `correctedLemma11_12Clean_of_stmt`. -/
theorem firstPass_11_12_clean
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
    (hDsm : SmallMetricDiameterLargeMassStmt.{u})
    (hMf : LQGMassInnerMeasurableFrozen.{u})
    (hDiam : LQGInternalDiamInnerMeasurableFrozen.{u})
    (hMk : DomainMarkovConditionalPositiveFrozen.{u})
    (hholder : GreenPotentialHolderStmt.{u}) :
    CorrectedLemma11_12CleanStmt.{u} :=
  correctedLemma11_12Clean_of_stmt
    (HarmonicBalls.S11m.Final11_12.firstPass_11_12_final hAx hLen hN2 hμW hLoc hCanon hNonat hExists hDG hCC hE
      hfr hmass hCMAbs hCMRew hComp hDsm hMf hDiam hMk hholder)

end HarmonicBalls.S11m.Clean11_12
