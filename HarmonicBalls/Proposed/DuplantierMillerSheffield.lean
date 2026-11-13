import Mathlib
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.LQGMetric

/-! # Literature input: Duplantier-Miller-Sheffield, Lemma A.10, whole-plane clause (proposed)

Source: J. Duplantier, J. Miller and S. Sheffield, *Liouville quantum gravity as a mating of trees*,
arXiv:1409.7055v4, Appendix A, Lemma A.10, printed page 184 (PDF page 184). The statement was checked against the
page image of arXiv:1409.7055v4; source check pending.

The whole-plane clause of Lemma A.10 reads: *if `h` is a whole-plane GFF with the additive constant fixed so that its
average on `∂D` is equal to `0`, then a sample from the law of `μ_h(D)dh` can be produced by sampling `h` according to
its unweighted law, then picking `z₀ ∈ D` according to Lebesgue measure, then adding to `h` the function
`z ↦ -γ log|z - z₀| + γ log max(|z|, 1)`, and then finally taking the additive constant so that the average of the
resulting field on `∂D` is equal to `0`.*

Here `D = B_1`, the disc of the paper's Palm identity (eq:r6-palm, r8 lines 1800-1815). Then `∂D` is the unit circle,
its average is the circle average `h_1(0)`, and the normalization "additive constant fixed" is the normalization
`h^ℂ_1(0) = 0` built into `IsWholePlaneGFF`. The clause is a statement about the law of the field only (unmarked).
The marked version used by eq:r6-palm (a point `z` weighting `μ_h(dz)`, for every Borel `Ψ(h,z)`) is NOT stated
for the whole plane in Lemma A.10: the statement's first paragraph (Dirichlet boundary conditions, open `U ⊆ D`) is
marked, and the proof says that the whole-plane case "follows from the same argument". This Prop does not include
that marked version. -/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The function `f_z(w) = -γ log|w - z| + γ log max(|w|, 1)` added to the field in the whole-plane clause of
Lemma A.10 (`z₀` there is `z` here). -/
noncomputable def dmsShift (γ : ℝ) (z w : ℂ) : ℝ :=
  -γ * Real.log ‖w - z‖ + γ * Real.log (max ‖w‖ 1)

/-- The additive constant `κ = -(h_1(0) + avg_{∂B_1} f_z)` taken at the end of the procedure, given the value
`h_1(0)` of the circle average of `h` on the unit circle. -/
noncomputable def dmsConstant (γ : ℝ) (z : ℂ) (h10 : ℝ) : ℝ :=
  -(h10 + Real.circleAverage (dmsShift γ z) 0 1)

/-- The raw pairing functional of the output `h + f_z + κ` of the sampling procedure, given the raw pairing
functional `T = (h, ·)` of `h` and the value `h_1(0)`. -/
noncomputable def dmsShiftedPairing (γ : ℝ) (z : ℂ) (T : (ℂ → ℝ) → ℝ) (h10 : ℝ) : (ℂ → ℝ) → ℝ :=
  fun φ => T φ + (∫ w, dmsShift γ z w * φ w) + dmsConstant γ z h10 * ∫ w, φ w

/-- No counted chain uses this normalized form; the counted chain uses
`DMSLemmaA10WholePlaneUnnormalized` (this file) and `DMSLemmaA10WholePlaneMarked`
(`FirstPass/Frozen/S11i.lean`). The right side divides by `(volume (ball 0 1)).toReal`, so for `F ≡ 1`
both sides equal `1`.

**Duplantier-Miller-Sheffield, Lemma A.10, whole-plane clause, for `D = B_1`** (arXiv:1409.7055v4, Appendix A,
p. 184), as a property of the whole-plane GFF `(P, hC, hcirc)` and of its γ-LQG measure `μ` with `α₀ = 0`.

"A sample from the law of `μ_h(D)dh`" is the probability law of the field under the weighting `μ_h(D)`, that is
`E[μ_h(D) F(h)] / E[μ_h(D)]`, tested against bounded measurable `F` on raw pairing functionals (measurable for
`pairingSigmaAlgebra`, the σ-algebra of the metric definition). The procedure's output law is the average over
`z ∈ B_1` (Lebesgue measure, normalized by `|B_1| = π`) of the unweighted law of `dmsShiftedPairing γ z (hC ·) (hcirc · 1 0)`. -/
def DMSLemmaA10WholePlane (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ F : ((ℂ → ℝ) → ℝ) → ℝ, Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ] F →
      (∃ C : ℝ, ∀ T, |F T| ≤ C) →
        (∫ ω, (μ ω (ball 0 1)).toReal * F (hC ω) ∂P) / (∫ ω, (μ ω (ball 0 1)).toReal ∂P) =
          (∫ z in ball (0 : ℂ) 1, ∫ ω, F (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) ∂P)
            / (volume (ball (0 : ℂ) 1)).toReal

/-- **Duplantier-Miller-Sheffield, Lemma A.10, whole-plane clause, unnormalized form** (arXiv:1409.7055v4, Appendix A,
p. 184, the last paragraph of the statement, with `D` the unit disk). The printed paragraph reads: if `h` is a
whole-plane GFF with the additive constant fixed so that its average on `∂D` is `0`, then a sample from the law of
`μ_h(D)dh` can be produced by sampling `h` according to its unweighted law, then picking `z₀ ∈ D` according to Lebesgue
measure, then adding to `h` the function `z ↦ -γ log|z - z₀| + γ log max(|z|,1)`, and then taking the additive constant
so that the average of the resulting field on `∂D` is `0`. It is read as unnormalized measures, as in the r10 proof of
`l:r9-marked` (reports: "These are unnormalized measures: P_g has mass one and d²z is ordinary Lebesgue measure"): the
measure `μ_h(D) dP(h)` equals the image of Lebesgue measure on `D`, times `P`, under the shift. Its total-mass
consequence `E[μ_h(B_1)] = π` is eq:r9-total-area of r10 (line 2613). The normalized-ratio form is
`DMSLemmaA10WholePlane` above. Source check pending. -/
def DMSLemmaA10WholePlaneUnnormalized {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ F : ((ℂ → ℝ) → ℝ) → ℝ, Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ] F →
      (∃ C : ℝ, ∀ T, |F T| ≤ C) →
        ∫ ω, (μ ω (ball 0 1)).toReal * F (hC ω) ∂P
          = ∫ z in ball (0 : ℂ) 1, ∫ ω, F (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) ∂P ∂volume

end HarmonicBalls
