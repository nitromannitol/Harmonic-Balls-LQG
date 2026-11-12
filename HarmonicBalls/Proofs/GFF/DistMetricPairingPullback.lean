import HarmonicBalls.Proofs.GFF.ContinuousShiftCircleBridge
import LatticeProb.Bonanno.LQGMetric.Statement.Metric

/-! # Metrics of distributions as metrics of pairing functionals

The space of distributions, the space of continuous metrics and the countable-coordinate
reconstruction used here are from Leonardo Bonanno's LatticeProb formalization.

A metric assignment `D` on distributions (`DistC → ContMetric`, as in Gwynne-Miller 2021,
Section 1.2, p. 6) induces a metric assignment on pairing functionals: reconstruct the distribution
from the pairings with test functions, then apply `D` (`pairingMetric`). The induced assignment is
measurable for the σ-algebra of test-function evaluations whenever `D` is Borel. For a whole-plane
GFF plus a random continuous function `f`, the reconstructed distribution is almost surely the
distribution-valued version of the field shifted by `f` (`shiftedReconstructedGFF`), which is a
whole-plane GFF plus a continuous function in the sense of Gwynne-Miller; hence the induced metric
of the field is almost surely `D` of that version. -/

noncomputable section
open MeasureTheory Filter
namespace HarmonicBalls

/-- Restriction of a pairing functional to the test functions of the space of distributions. -/
def testRestriction (T : (ℂ → ℝ) → ℝ) : LQGMetric.TestC → ℝ := fun φ => T φ

theorem testRestriction_comap_le :
    MeasurableSpace.comap testRestriction MeasurableSpace.pi ≤ distributionMeasurableSpace := by
  unfold distributionMeasurableSpace
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂_of_le (φ : ℂ → ℝ) ⟨φ.contDiff, φ.hasCompactSupport, Set.subset_univ _⟩ le_rfl

theorem measurable_testRestriction : Measurable[distributionMeasurableSpace] testRestriction :=
  measurable_iff_comap_le.2 testRestriction_comap_le

/-- The distribution reconstructed from the pairings of a pairing functional with test functions. -/
def pairingDistribution (T : (ℂ → ℝ) → ℝ) : LQGMetric.DistC :=
  fullTestDistributionVersion (testRestriction T)

theorem measurable_pairingDistribution :
    Measurable[distributionMeasurableSpace] pairingDistribution :=
  measurable_fullTestDistributionVersion.comp measurable_testRestriction

/-- The pairing functional of a distribution reconstructs to that distribution. -/
theorem pairingDistribution_distributionPairingExtension (T : LQGMetric.DistC) :
    pairingDistribution (distributionPairingExtension T) = T := by
  have he : testRestriction (distributionPairingExtension T) = fun φ => T φ := by
    funext φ
    exact distributionPairingExtension_test T φ
  rw [pairingDistribution, he, fullTestDistributionVersion_pairings]

/-- The metric assignment on pairing functionals induced by a metric assignment on distributions. -/
def pairingMetric (D : LQGMetric.DistC → LQGMetric.ContMetric) (T : (ℂ → ℝ) → ℝ) (u v : ℂ) : ℝ :=
  (D (pairingDistribution T)).1 (u, v)

/-- A Borel metric assignment on distributions induces a metric assignment on pairing functionals
whose evaluations are measurable for the σ-algebra of test-function evaluations. -/
theorem measurable_pairingMetric_apply {D : LQGMetric.DistC → LQGMetric.ContMetric}
    (hD : Measurable D) (u v : ℂ) :
    Measurable[distributionMeasurableSpace] fun T => pairingMetric D T u v :=
  (ContinuousMap.measurable_eval (u, v)).comp
    (measurable_subtype_coe.comp (hD.comp measurable_pairingDistribution))

theorem pairingMetric_distributionPairingExtension (D : LQGMetric.DistC → LQGMetric.ContMetric)
    (T : LQGMetric.DistC) (u v : ℂ) :
    pairingMetric D (distributionPairingExtension T) u v = (D T).1 (u, v) := by
  rw [pairingMetric, pairingDistribution_distributionPairingExtension]

/-- At each fixed test function, the shifted distribution-valued version pairs almost surely like
the raw pairing functional of the field plus the continuous function. -/
theorem IsWholePlaneGFF.ae_shiftedReconstructedGFF_apply
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (φ : LQGMetric.TestC) :
    ∀ᵐ ω ∂P, shiftedReconstructedGFF hC f hf ω φ = addFunPairing (hC ω) (f ω) φ := by
  filter_upwards [hh.ae_reconstructFullTest_randomShift f hf,
    hh.ae_reconstructFullTest_randomShift_apply f hf φ] with ω hs hv
  rw [← hv, hs]
  rfl

/-- For a whole-plane GFF plus a random continuous function, the distribution reconstructed from the
pairings is almost surely the shifted distribution-valued version of the field. -/
theorem IsWholePlaneGFF.ae_pairingDistribution_addFunPairing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) :
    ∀ᵐ ω ∂P, pairingDistribution (addFunPairing (hC ω) (f ω)) = shiftedReconstructedGFF hC f hf ω :=
  hh.ae_reconstructFullTest_randomShift f hf

/-- The induced metric of a whole-plane GFF plus a random continuous function is almost surely the
metric of the shifted distribution-valued version, simultaneously at all pairs of points. -/
theorem IsWholePlaneGFF.ae_pairingMetric_addFunPairing
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (D : LQGMetric.DistC → LQGMetric.ContMetric)
    (f : Ω → ℂ → ℝ) (hf : ∀ ω, Continuous (f ω)) :
    ∀ᵐ ω ∂P, ∀ u v : ℂ, pairingMetric D (addFunPairing (hC ω) (f ω)) u v =
      (D (shiftedReconstructedGFF hC f hf ω)).1 (u, v) := by
  filter_upwards [hh.ae_pairingDistribution_addFunPairing f hf] with ω hω u v
  rw [pairingMetric, hω]

/-- A whole-plane GFF plus a random continuous function reconstructs almost surely to a whole-plane
GFF plus a continuous function in the sense of Gwynne-Miller 2021 (Section 1.2, p. 6). -/
theorem IsWholePlaneGFF.isGFFPlusCont_and_ae_pairingDistribution
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (f : Ω → ℂ → ℝ)
    (hf : ∀ ω, Continuous (f ω)) (hm : ∀ z, Measurable fun ω => f ω z) :
    LQGMetric.IsGFFPlusCont (shiftedReconstructedGFF hC f hf) P ∧
      ∀ᵐ ω ∂P, pairingDistribution (addFunPairing (hC ω) (f ω)) =
        shiftedReconstructedGFF hC f hf ω :=
  ⟨hh.shiftedReconstructedGFF_isGFFPlusCont f hf hm, hh.ae_pairingDistribution_addFunPairing f hf⟩

end HarmonicBalls
