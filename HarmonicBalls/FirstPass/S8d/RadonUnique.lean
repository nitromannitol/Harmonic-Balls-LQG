import HarmonicBalls.FirstPass.Frozen.S8d
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-! # helper: the Radon-uniqueness input is a theorem

`RadonIntegralUniqueFrozen` (FirstPass/Frozen/S8d.lean) asks that two locally finite measures on `ℂ` with the same
integrals against all continuous compactly supported real functions are equal. This is the uniqueness part of the Riesz
representation theorem (Rudin, Real and Complex Analysis, Thm 2.14), and Mathlib proves it for regular measures as
`MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported` (Integral/RieszMarkovKakutani/Real.lean). Locally finite
Borel measures on `ℂ` are regular, so the frozen proposition is proved here and is no longer an external input. -/

open MeasureTheory

namespace HarmonicBalls

/-- The Radon-uniqueness proposition, proved from Mathlib's Riesz-Markov uniqueness. -/
theorem radonIntegralUnique_proved : RadonIntegralUniqueFrozen := by
  intro m m' _ _ h
  exact MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported
    (fun g => h (g : ℂ → ℝ) g.continuous g.hasCompactSupport)

end HarmonicBalls
