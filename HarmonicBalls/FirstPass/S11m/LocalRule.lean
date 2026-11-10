import HarmonicBalls.FirstPass.S11h.LocalEvents
import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.Steps.Sec11.MetricConstantScaling

/-!
# Homogeneity of the local certificate rule (fp-S11m, owner z4)

Route `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 2 and section 5: the explicit certificate
`E₁ = {L > A, a₀ > d₀}`, `E₂ = {a₁ > d₁, μ(U) > M S}`, `E₃ = {a₂ > d₂}` (equation (2)) is invariant under independent
positive rescalings `μ ↦ a μ`, `D ↦ c D` (equation (3)). This file proves that invariance for the local events of
`FirstPass/S11h/LocalEvents.lean`, which is what lets the decoded measure `a • μ` and the decoded metric `c • D` (with
random constants `a, c > 0` from the decoders) be replaced by the true pair in the rule. Deterministic; no inputs.
-/

noncomputable section

namespace HarmonicBalls.S11m.LocalRule

open MeasureTheory Set Metric
open scoped ENNReal

/-- Cancellation of a finite nonzero factor in a strict inequality in `ℝ≥0∞`. -/
theorem ennreal_mul_lt_mul_iff_of_ne {a x y : ℝ≥0∞} (ha0 : a ≠ 0) (haT : a ≠ ⊤) : a * x < a * y ↔ x < y := by
  constructor
  · intro h
    refine not_le.1 fun hle => ?_
    have h' : a * y ≤ a * x := by gcongr
    exact absurd h (not_lt.2 h')
  · exact fun h => ENNReal.mul_lt_mul_right ha0 haT h

/-- Positive homogeneity of the internal diameter `diam^δ_D(A)`, for the internal metric of `B_δ(A)`. -/
theorem internalDiam_const_mul (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (δ : ℝ) (A : Set ℂ) :
    internalDiam (fun x y => c * D x y) δ A = ENNReal.ofReal c * internalDiam D δ A := by
  unfold internalDiam
  simp only [internalMetric_const_mul D hc, ← ENNReal.mul_iSup]

/-- Positive homogeneity of `a₀ = D(0, ∂B_δ)`-type quantities `pinchLocalA`. -/
theorem pinchLocalA_const_mul (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (W Q : Set ℂ) (δ : ℝ) :
    pinchLocalA (fun x y => c * D x y) W Q δ = ENNReal.ofReal c * pinchLocalA D W Q δ := by
  unfold pinchLocalA
  simp only [internalMetric_const_mul D hc, ← ENNReal.mul_iSup]

/-- Positive homogeneity of `L = D(Q̄', ∂Q)`. -/
theorem pinchLocalL_const_mul (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (Q' Q : Set ℂ) :
    pinchLocalL (fun x y => c * D x y) Q' Q = c * pinchLocalL D Q' Q :=
  HarmonicBalls.S11n.setDist_smul_left hc.le D _ _

/-- The first local event is invariant under `D ↦ c D`, `c > 0`. -/
theorem pinchFirstEventLocal_const_mul_iff (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (W T Q' Q : Set ℂ) (δ : ℝ) :
    pinchFirstEventLocal (fun x y => c * D x y) W T Q' Q δ ↔ pinchFirstEventLocal D W T Q' Q δ := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold pinchFirstEventLocal
  rw [pinchLocalA_const_mul D hc, pinchLocalL_const_mul D hc, ENNReal.ofReal_mul hc.le,
    internalDiam_const_mul D hc, HarmonicBalls.S11n.setDist_smul_left hc.le D, ENNReal.ofReal_mul hc.le,
    ennreal_mul_lt_mul_iff_of_ne hc0 hcTop, ennreal_mul_lt_mul_iff_of_ne hc0 hcTop]

/-- The third local event is invariant under `D ↦ c D`, `c > 0`. -/
theorem pinchThirdEventLocal_const_mul_iff (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (V W : Set ℂ) (δ : ℝ) :
    pinchThirdEventLocal (fun x y => c * D x y) V W δ ↔ pinchThirdEventLocal D V W δ := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold pinchThirdEventLocal
  rw [internalDiam_const_mul D hc, HarmonicBalls.S11n.setDist_smul_left hc.le D, ENNReal.ofReal_mul hc.le,
    ennreal_mul_lt_mul_iff_of_ne hc0 hcTop]

/-- The second local event is invariant under `μ ↦ a μ` and `D ↦ c D`, `a, c > 0`. -/
theorem pinchSecondEventLocal_smul_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (U V : Set ℂ) (δ M : ℝ) :
    pinchSecondEventLocal (ENNReal.ofReal a • μ) (fun x y => c * D x y) U V δ M ↔
      pinchSecondEventLocal μ D U V δ M := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  have haTop : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold pinchSecondEventLocal
  rw [internalDiam_const_mul D hc, HarmonicBalls.S11n.setDist_smul_left hc.le D, ENNReal.ofReal_mul hc.le,
    ennreal_mul_lt_mul_iff_of_ne hc0 hcTop, HarmonicBalls.S11n.annulusGreenPotentialSup_smul,
    Measure.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm (ENNReal.ofReal M), mul_assoc,
    ennreal_mul_lt_mul_iff_of_ne ha0 haTop]

/-- The local certificate rule `E₁ ∩ E₂(M) ∩ E₃` of equation (2) for the pair `(μ, D)`. -/
def pinchLocalRule (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (W T Q' Q U V : Set ℂ) (δ M : ℝ) : Prop :=
  pinchFirstEventLocal D W T Q' Q δ ∧ pinchSecondEventLocal μ D U V δ M ∧ pinchThirdEventLocal D V W δ

/-- Equation (3): the certificate rule is invariant under independent positive rescalings of the measure and of the
metric. This is what lets the decoded pair `(a • μ, c • D)` stand in for `(μ, D)`. -/
theorem pinchLocalRule_smul_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (W T Q' Q U V : Set ℂ) (δ M : ℝ) :
    pinchLocalRule (ENNReal.ofReal a • μ) (fun x y => c * D x y) W T Q' Q U V δ M ↔
      pinchLocalRule μ D W T Q' Q U V δ M := by
  unfold pinchLocalRule
  rw [pinchFirstEventLocal_const_mul_iff D hc, pinchSecondEventLocal_smul_iff μ D ha hc,
    pinchThirdEventLocal_const_mul_iff D hc]

end HarmonicBalls.S11m.LocalRule

end
