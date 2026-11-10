import HarmonicBalls.FirstPass.S11i.Step8TransferDilation
import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Defs.LQGMetric

/-!
# Every `hzoom(k)` from the unit-ball frequency, with the normalized zoomed model (fp-S11i-hzoom-scale, owner n4)

Source: ChatGPT chat 196 (PRO), decision D3, `notes/fp-gaps/CHATGPT-hb-11-13-blockers.md` section 4 (l.460-634) and its
final dependency decision, item 6. The family hypothesis `hzoom` of `hphys_of_zoom_const_family`
(`S11i/Step8TransferDilation.lean`) is obtained for every `k`, not only for the unit scale, from the unit-ball frequency
of the NORMALIZED model at scale `R = 2^k`. No marked DMS theorem on `B_{2^k}` is used.

Route, per `k` with `R = 2^k`:
* 4.1 normalization. `normField R hC hcirc` and `normCirc R hcirc` are the affine renormalization of the whole-plane GFF with
  `a = R`, `b = 0` (`WholePlaneGFFAffineInvariance`, derived in `S11v/Affine.lean`). They are a whole-plane GFF
  (`isWholePlaneGFF_normalized`, no input). The LQG measure of the normalized field is
  `normMeasure γ μ hcirc k ω = e^{-γ C_k(ω)} · zoomMeasure (μ ω) k`, with `C_k = hcirc ω R 0 + Q log R`. Its limit property
  comes from the Proposed input `LQGMeasureCoordChange` (`Proposed/LQG.lean`, pending operator source-check) and the constant
  shift `isLQGLimit_add_const` (proved here).
* 4.2 scale transfer. `hzoom_all_of_unit_models`: the constants are `a = e^{-γ C_k}` and `b = B⁻¹`, where `B` is the metric
  constant of the zoom.
* 4.3 unit ball. The unit-ball frequency statement of every normalized model is the hypothesis `UnitBallFrequencyModelsStmt`.
  It is NOT proved here: it is where the frozen `DMSLemmaA10WholePlaneMarked` and the unit-scale hFit/hCov/hFdef argument
  enter (see the report).
* The metric normalization (Fact 2.2 III-IV for the renormalized field) is the hypothesis `ZoomMetricNormStmt`, not proved here.
-/

open MeasureTheory Filter Topology Set Metric HarmonicBalls
open scoped ENNReal
open HarmonicBalls.FirstPassS11iStep8Zoom FirstPassS11i

namespace HarmonicBalls.FirstPassS11iHzoom

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The whole-plane pairing renormalized at the real scale `R`: `φ ↦ (|R|²)⁻¹ hC(φ((·)/R)) - hcirc R 0 ∫ φ`. This is the
pairing of `WholePlaneGFFAffineInvariance` for `a = R` (as a complex number) and `b = 0`. -/
noncomputable def normField (R : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (φ : ℂ → ℝ) : ℝ :=
  (‖(R : ℂ)‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - 0) / (R : ℂ))) - hcirc ω ‖(R : ℂ)‖ 0 * ∫ x, φ x

/-- The circle averages of the renormalized field: `(r, z) ↦ hcirc (R r) (R z) - hcirc R 0`. -/
noncomputable def normCirc (R : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) (r : ℝ) (z : ℂ) : ℝ :=
  hcirc ω (‖(R : ℂ)‖ * r) ((R : ℂ) * z + 0) - hcirc ω ‖(R : ℂ)‖ 0

/-- **Normalized whole-plane GFF.** For `R ≠ 0`, the renormalized field is a whole-plane GFF. This is the affine invariance
of the whole-plane GFF (paper, eq:gff-scaling, line 369), derived in `S11v/Affine.lean` from `IsWholePlaneGFF` alone. -/
theorem isWholePlaneGFF_normalized {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {R : ℝ} (hR : R ≠ 0) :
    IsWholePlaneGFF P (normField R hC hcirc) (normCirc R hcirc) :=
  wholePlaneGFFAffineInvariance_derived P hC hcirc hG (R : ℂ) (Complex.ofReal_ne_zero.mpr hR) 0

/-- **Constant shift of an LQG limit.** If `m` is the LQG limit of `hε`, then `e^{γc} · m` is the LQG limit of `hε + c`:
the approximations `ε^{γ²/2} e^{γ (hε + c)} dz` are `e^{γc}` times the approximations of `hε`, and the vague limit is linear. -/
theorem isLQGLimit_add_const {γ c : ℝ} {hε : ℝ → ℂ → ℝ} {m : Measure ℂ} (h : IsLQGLimit γ hε m) :
    IsLQGLimit γ (fun ε z => hε ε z + c) (ENNReal.ofReal (Real.exp (γ * c)) • m) := by
  have hden : ∀ ε : ℝ, lqgApprox γ (fun ε z => hε ε z + c) ε =
      ENNReal.ofReal (Real.exp (γ * c)) • lqgApprox γ hε ε := by
    intro ε
    ext s hs
    simp only [lqgApprox, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    congr 1
    rw [mul_add, Real.exp_add]
    ring
  refine
    { isLocallyFiniteMeasure := ⟨fun x => ?_⟩
      tendsto_integral := fun f hf hcs => ?_ }
  · obtain ⟨s, hs, hms⟩ := h.isLocallyFiniteMeasure.finiteAtNhds x
    exact ⟨s, hs, by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hms⟩
  · have hT := h.tendsto_integral f hf hcs
    simp only [hden, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    exact hT.const_mul _

/-- **LQG measure of the normalized field (ruling 4.1, measure side).** `normMeasure γ μ hcirc k ω` is
`e^{-γ C_k(ω)} · zoomMeasure (μ ω) k`, with `C_k(ω) = hcirc ω 2^k 0 + Q log 2^k`. It is the LQG measure of the renormalized
field `normCirc (2^k) hcirc`. -/
noncomputable def normMeasure (γ : ℝ) (μ : Ω → Measure ℂ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) (ω : Ω) : Measure ℂ :=
  ENNReal.ofReal (Real.exp (-(γ * (hcirc ω ((2 : ℝ) ^ k) 0 + lqgQ γ * Real.log ((2 : ℝ) ^ k))))) •
    zoomMeasure (μ ω) k

/-- The normalized LQG measure is the LQG measure of the normalized field. The input is the coordinate change `LQGMeasureCoordChange`
(`Proposed/LQG.lean`, Fact 2.1 IV, pending source-check), applied at `a = 2^k`, `b = 0`, and the constant shift above. -/
theorem isLQGMeasureOfField_normMeasure {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) (k : ℕ) :
    IsLQGMeasureOfField P γ 0 (normCirc ((2 : ℝ) ^ k) hcirc) (normMeasure γ μ hcirc k) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hae := hCC hG hγ0 hγ2 hQ μ hμ
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  unfold IsLQGMeasureOfField IsLQGMeasure
  filter_upwards [hae] with ω hω
  have hne : (((2 : ℝ) ^ k : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have h := hω _ hne 0
  have hnorm : ‖(((2 : ℝ) ^ k : ℝ) : ℂ)‖ = (2 : ℝ) ^ k := by
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have key := isLQGLimit_add_const (γ := γ)
    (c := -(hcirc ω ((2 : ℝ) ^ k) 0 + lqgQ γ * Real.log ((2 : ℝ) ^ k))) h
  convert key using 2
  all_goals first
    | simp only [normMeasure, zoomMeasure, sub_zero, ENNReal.ofReal_one, one_smul, mul_neg]
    | (funext z; simp only [fieldCircleAverage, normCirc, zero_mul, sub_zero, add_zero, hnorm]; ring_nf)

/-- A unit-ball frequency statement for the model `(μ, D)`: for `P`-a.e. `ω` and `μ ω`-a.e. `w ∈ B₁(0)`, the window count
frequency of the certificate events at radii `2⁻ⁿ` tends to `q`. -/
def UnitBallFrequencyStmt (P : Measure Ω) (q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, ∀ᵐ w ∂(μ ω), w ∈ ball (0 : ℂ) 1 →
    Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) /
        (N : ℝ)) atTop (𝓝 q)

/-- **INPUT (pending): unit-ball frequency for every whole-plane LQG model.** For every whole-plane GFF `hC'`, LQG measure
`μ'` of `hcirc'` and LQG metric `D'` of `hC'` (`IsLQGMetricOfField`, `α₀ = 0`), the unit-ball frequency statement holds. This is
the unit-scale output of Lemma 11.13 (paper, Step 8) obtained from the frozen marked identity `DMSLemmaA10WholePlaneMarked`
(DMS Lemma A.10, arXiv:1409.7055 Appendix A p. 184) together with the unit-scale hFit/hCov/hFdef argument. Not proved in this
repository; see the report. -/
def UnitBallFrequencyModelsStmt (P : Measure Ω) (γ ξ q : ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) : Prop :=
  ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ) (D' : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC' hcirc' → IsLQGMeasureOfField P γ 0 hcirc' μ' → IsLQGMetricOfField P γ ξ 0 hC' D' →
      UnitBallFrequencyStmt P q U V W T Q' Q δ M μ' D'

/-- **INPUT (pending): metric normalization at every scale.** For every `k`, the renormalized field `normField (2^k) hC hcirc`
has an LQG metric `Dk` whose zoom relation holds: `zoomMetric (D ω) k = B · Dk ω` with `B > 0` almost surely. This is Fact 2.2
III-IV (weyl scaling and coordinate change of the metric, paper lines 432-457) for the renormalized field. Not proved here. -/
def ZoomMetricNormStmt (P : Measure Ω) (γ ξ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ Dk : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ 0 (normField ((2 : ℝ) ^ k) hC hcirc) Dk ∧
    ∀ᵐ ω ∂P, ∃ B : ℝ, 0 < B ∧ ∀ x y, zoomMetric (D ω) k x y = B * Dk ω x y

/-- **Every `hzoom(k)`, from the unit-ball frequency of the normalized models (ruling 4.2).** For each `k`, almost surely
there are positive constants `a, b` such that the zoomed pair `(a · zoomMeasure (μ ω) k, b · zoomMetric (D ω) k)` has the
unit-ball frequency `q` on `B₁(0)`. This is the family hypothesis `hzoom` of `hphys_of_zoom_const_family`. The constants are
`a = e^{-γ C_k}` (measure) and `b = B⁻¹` (metric). -/
theorem hzoom_all_of_unit_models {P : Measure Ω} {γ ξ q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) (hMetric : ZoomMetricNormStmt P γ ξ hC hcirc D)
    (hunit : UnitBallFrequencyModelsStmt P γ ξ q U V W T Q' Q δ M) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᵐ w ∂(ENNReal.ofReal a • zoomMeasure (μ ω) k), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          CertificateEvent (ENNReal.ofReal a • zoomMeasure (μ ω) k) (fun x y => b * zoomMetric (D ω) k x y)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) / (N : ℝ))
          atTop (𝓝 q) := by
  intro k
  obtain ⟨Dk, hDk, hscale⟩ := hMetric k
  have hR : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hGk := isWholePlaneGFF_normalized hG hR
  have hμk := isLQGMeasureOfField_normMeasure hγ0 hγ2 hG hμ hCC k
  have hU := hunit (normField ((2 : ℝ) ^ k) hC hcirc) (normCirc ((2 : ℝ) ^ k) hcirc)
    (normMeasure γ μ hcirc k) Dk hGk hμk hDk
  filter_upwards [hU, hscale] with ω hω hsc
  obtain ⟨B, hB, hBeq⟩ := hsc
  have hmet : (fun x y => B⁻¹ * zoomMetric (D ω) k x y) = Dk ω := by
    funext x y
    rw [hBeq x y, ← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]
  refine ⟨Real.exp (-(γ * (hcirc ω ((2 : ℝ) ^ k) 0 + lqgQ γ * Real.log ((2 : ℝ) ^ k)))), B⁻¹,
    Real.exp_pos _, inv_pos.mpr hB, ?_⟩
  have hmeas : ENNReal.ofReal (Real.exp (-(γ * (hcirc ω ((2 : ℝ) ^ k) 0 +
      lqgQ γ * Real.log ((2 : ℝ) ^ k))))) • zoomMeasure (μ ω) k = normMeasure γ μ hcirc k ω := rfl
  rw [hmeas, hmet]
  exact hω

/-- **The composite consumed by `hphys` (ruling 4.2 with `hphys_of_zoom_const_family`).** The unit-ball frequency of the
normalized models gives, for every `k` and `P`-a.e. `ω`, the physical window frequency of `(μ ω, D ω)` on `B_{2^k}(0)`. -/
theorem hphys_of_unit_models {P : Measure Ω} {γ ξ q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) (hMetric : ZoomMetricNormStmt P γ ξ hC hcirc D)
    (hunit : UnitBallFrequencyModelsStmt P γ ξ q U V W T Q' Q δ M) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) ((2 : ℝ) ^ k) →
      Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ) ^ k * (2 : ℝ)⁻¹ ^ n) z}.ncard : ℕ) : ℝ) / (N : ℝ)) atTop (𝓝 q) :=
  HarmonicBalls.FirstPassS11iStep8Transfer.hphys_of_zoom_const_family P U V W T Q' Q δ M q μ D
    (hzoom_all_of_unit_models hγ0 hγ2 hG hμ hCC hMetric hunit)

end HarmonicBalls.FirstPassS11iHzoom
