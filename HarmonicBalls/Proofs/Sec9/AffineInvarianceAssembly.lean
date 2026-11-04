import HarmonicBalls.Proofs.Sec9.AffinePairingCovariance
import HarmonicBalls.Proofs.Sec9.DyadicGlobalUniqueness

/-! # Whole-plane GFF affine invariance and weak uniqueness

The affine-invariance input follows from the covariance characterization of
the whole-plane field. The Section 6 and Section 8 inputs remain explicit.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Affine invariance follows from the defining covariance of the normalized
whole-plane GFF. -/
theorem wholePlaneGFFAffineInvariance_proved
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    WholePlaneGFFAffineInvariance P hC hcirc := by
  intro h a ha b
  exact h.complex_affine ha b

/-- Weak Proposition 9.2 from volume growth and Lemma 8.2, with affine
invariance discharged from the field's covariance characterization. -/
theorem subharmonicBallUniquenessWeak_of_volumeGrowth_typicalScales
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    SubharmonicBallUniquenessWeakStmt.{u} :=
  subharmonicBallUniquenessWeak_of_dyadic_volumeGrowth hI2 h82
    (fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc)

end HarmonicBalls
