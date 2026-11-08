import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAKernelBox

/-! # Route (A), C2': the second moment of the pairings of the whole-plane GFF

For a whole-plane GFF `(hC, hcirc)` (`IsWholePlaneGFF`, `HarmonicBalls/Defs/GFF.lean`) and a test function `f`
supported in a disc `ball 0 M`, the pairing `(h, f)` is centred with covariance `wholePlaneGFFCov (pairing f)
(pairing f)` (`covariance_eq`). Its second moment is therefore bounded by the Schur bound of
`RouteAKernelBox.lean`: `E[(h, f)²] ≤ (2 K_M) ∫ f²`. The centring makes the probabilistic covariance equal to the
second moment `∫ (h,f)²`; no integrability of the square is needed for this inequality.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- **Second moment of a pairing of the whole-plane GFF (route (A), C2').** For a test function `f` supported in
`ball 0 M` and bounded by `B`, `E[(h, f)²] ≤ (2 K_M) ∫ f²` (`K_M = kernelBoxConst M`). -/
theorem IsWholePlaneGFF.integral_sq_pairing_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {f : ℂ → ℝ} (hf : IsTestFunction Set.univ f) {M B : ℝ}
    (hsupp : ∀ x, x ∉ ball (0 : ℂ) M → f x = 0) (hB : ∀ x, |f x| ≤ B) :
    ∫ ω, (hC ω f) ^ 2 ∂P ≤ (2 * kernelBoxConst M).toReal * ∫ x, f x ^ 2 := by
  have hadm : (GFFObservable.pairing f).IsAdmissible := hf
  have hmean : ∫ ω, hC ω f ∂P = 0 := hG.integral_eq_zero (GFFObservable.pairing f) hadm
  have hcov : covariance (fun ω => hC ω f) (fun ω => hC ω f) P
      = wholePlaneGFFCov (GFFObservable.pairing f) (GFFObservable.pairing f) :=
    hG.covariance_eq (GFFObservable.pairing f) (GFFObservable.pairing f) hadm hadm
  have hsq : covariance (fun ω => hC ω f) (fun ω => hC ω f) P = ∫ ω, (hC ω f) ^ 2 ∂P := by
    unfold covariance
    simp only [hmean, sub_zero, sq]
  have hfm : Measurable f := hf.1.continuous.measurable
  calc ∫ ω, (hC ω f) ^ 2 ∂P
      = covariance (fun ω => hC ω f) (fun ω => hC ω f) P := hsq.symm
    _ = wholePlaneGFFCov (GFFObservable.pairing f) (GFFObservable.pairing f) := hcov
    _ ≤ |wholePlaneGFFCov (GFFObservable.pairing f) (GFFObservable.pairing f)| := le_abs_self _
    _ ≤ (2 * kernelBoxConst M).toReal * ∫ x, f x ^ 2 := abs_wholePlaneGFFCov_pairing_le hfm hsupp hB

end HarmonicBalls

end
