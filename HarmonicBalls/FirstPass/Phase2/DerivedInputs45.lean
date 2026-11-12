import HarmonicBalls.FirstPass.Phase2.CampbellDerivedWrappers
import HarmonicBalls.FirstPass.Phase2.ConeBadScalesHolds
import HarmonicBalls.FirstPass.Phase2.DerivedInputs43
import HarmonicBalls.FirstPass.Phase2.DerivedInputs44

/-!
# Derived-input forms, round 45: unused hypotheses removed

Each theorem below has the conclusion of the declaration named in its docstring and a subset of its hypotheses:
the conclusion already follows from that subset by theorems of this repository. The kept hypotheses are
unchanged; the proofs are chains of applications.

Generated from the types of the wrapped declarations; do not edit by hand.
-/

universe u

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-- `ManyConeBadScalesStmt` with no hypothesis; the hypotheses `hFreq`, `hTr` of `firstPass_11_7_derivedInputs43` are not used. -/
theorem firstPass_11_7_derivedInputs45 :
    ManyConeBadScalesStmt.{u} := by
  exact HarmonicBalls.manyConeBadScalesStmt_holds.{u}

/-- `LiouvilleVolumeGrowthStmt` with no hypothesis; the hypotheses `h` of `liouvilleVolumeGrowthStmt_of_ballMass` are not used. -/
theorem liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs45 :
    LiouvilleVolumeGrowthStmt.{u} := by
  exact HarmonicBalls.liouvilleVolumeGrowthStmt_of_ballMass_derivedInputs43.{u}

/-- `SubharmonicBallUniquenessWeakStmt` with no hypothesis; the hypotheses `hDG`, `hCC`, `hW`, `hE`, `hN`, `h82` of `firstPass_9_2_corrected` are not used. -/
theorem firstPass_9_2_corrected_derivedInputs45 :
    SubharmonicBallUniquenessWeakStmt.{u} := by
  exact HarmonicBalls.firstPass_9_2_corrected_derivedInputs43.{u}

/-- `PinchSecondEventFaithfulStmt` from the hypotheses `hAx`, `hD` of `firstPass_11_16_corrected_derivedInputs39` alone:
the hypotheses `hholder`, `hNa0`, `hNa`, `hPos` of that declaration are not used. -/
theorem firstPass_11_16_corrected_derivedInputs45
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hD : SmallMetricDiameterLargeMassStmt.{u}) :
    PinchSecondEventFaithfulStmt.{u} := by
  exact HarmonicBalls.firstPass_11_16_corrected_derivedInputs44.{u} (hAx := hAx) (hD := hD)

/-- `PinchThirdEventFaithfulStmt` from the hypotheses `h16`, `hAx` of `firstPass_11_17_corrected_derivedInputs38` alone:
the hypothesis `hdec` of that declaration is not used. -/
theorem firstPass_11_17_corrected_derivedInputs45
    (h16 : PinchSecondEventFaithfulStmt.{u})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchThirdEventFaithfulStmt.{u} := by
  exact HarmonicBalls.firstPass_11_17_corrected_derivedInputs43.{u} (h16 := h16) (hAx := hAx)

/-- `HarmonicBallNoveltyCanonicalStmt` from the hypotheses `hjordan`, `hmetric` of `harmonicBallNoveltyStmt_of_existence_and_results_canonical` alone:
the hypotheses `hex`, `hlip` of that declaration are not used. -/
theorem harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs45
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hmetric : HarmonicBallNotMetricBallCanonicalStmt.{u}) :
    HarmonicBallNoveltyCanonicalStmt.{u} := by
  exact HarmonicBalls.harmonicBallNoveltyStmt_of_existence_and_results_canonical_derivedInputs43.{u} (hjordan := hjordan) (hmetric := hmetric)

/-- `HarmonicBallNotMetricBallCanonicalStmt` from the hypotheses `hmany`, `hmetricAxioms` of `harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth` alone:
the hypotheses `hbound`, `hgrowth` of that declaration are not used. -/
theorem harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs45
    (hmany : Closure.ManyPinchScalesCanonicalModelStmt.{u})
    (hmetricAxioms : ∀ (γ α₀ ξ : ℝ), LT.lt.{0} 0 γ → LT.lt.{0} γ 2 → LT.lt.{0} α₀ (lqgQ γ) → ∀ (Ω : Type u) [MeasurableSpace.{u} Ω] (P : Measure.{u} Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF.{u} P hC hcirc → LQGMetricFieldAxioms.{u} P γ ξ α₀ hC hcirc) :
    HarmonicBallNotMetricBallCanonicalStmt.{u} := by
  exact HarmonicBalls.harmonicBallNotMetricBallCanonicalStmt_of_comparison_pinch_and_volumeGrowth_derivedInputs43.{u} (hmany := hmany) (hmetricAxioms := hmetricAxioms)

end HarmonicBalls

namespace HarmonicBalls.Closure

/-- `OriginManyGoodScalesStmt` with no hypothesis; the hypotheses `hholder` of `closure_8_3_derivedInputs43` are not used. -/
theorem closure_8_3_derivedInputs45 :
    OriginManyGoodScalesStmt.{u} := by
  exact HarmonicBalls.Closure.closure_8_3_derivedInputs44.{u}

/-- `SubharmonicBallUniquenessC51Stmt` with no hypothesis; the hypotheses `hSub`, `hDG` of `closure_9_2_derivedInputs41` are not used. -/
theorem closure_9_2_derivedInputs45 :
    S9c.SubharmonicBallUniquenessC51Stmt.{u} := by
  have d1 := HarmonicBalls.dmsLemmaA10WholePlaneMarkedSub_forall.{u}
  exact HarmonicBalls.Closure.closure_9_2_derivedInputs43.{u} (hSub := d1)

end HarmonicBalls.Closure
