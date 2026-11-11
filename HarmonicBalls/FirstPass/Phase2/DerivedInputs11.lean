import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.Proposed.LQG

/-!
# Derived inputs, batch 11 (fp-phase2-inventory-map-1; worker z7)

Binder-free restatement `HarmonicBalls.WholePlaneGFFAffineInvariance_derived` of the Proposed Prop
`HarmonicBalls.WholePlaneGFFAffineInvariance` (Proposed/LQG.lean:56), written in the universal form that the counted
binders use (`FirstPass/Closure/PaperExponent.lean:130`): `∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
(hC) (hcirc), WholePlaneGFFAffineInvariance P hC hcirc`. The Prop is written exactly as in its declaration; the
proof is glue to `HarmonicBalls.wholePlaneGFFAffineInvariance_derived` (FirstPass/S11v/Affine.lean:145), which
derives it from `IsWholePlaneGFF` alone.

Inventory row 10 of docs/campaign/PHASE2-INVENTORY.md section 2. Row 5 (`LQGMeasureWeylScaling`) is discharged in
DerivedInputs10 by worker z6 and is not repeated here.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Binder-free form of the affine invariance of the whole-plane GFF (Proposed/LQG.lean:56), with `Ω` explicit as
in the counted binders. Glue only: `wholePlaneGFFAffineInvariance_derived` with the universe fixed to `u`. -/
theorem WholePlaneGFFAffineInvariance_derived :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc := by
  intro Ω _ P hC hcirc
  exact wholePlaneGFFAffineInvariance_derived P hC hcirc

end HarmonicBalls
