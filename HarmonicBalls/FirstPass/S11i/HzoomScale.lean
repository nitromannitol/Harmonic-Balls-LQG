import HarmonicBalls.FirstPass.S11i.Step8TransferDilation
import HarmonicBalls.FirstPass.S11v.Affine
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Defs.LQGMetric

/-!
# Every `hzoom(k)` from the unit-ball frequency, with the normalized zoomed model

The family hypothesis `hzoom` of `hphys_of_zoom_const_family`
(`S11i/Step8TransferDilation.lean`) is obtained for every `k`, not only for the unit scale, from the unit-ball frequency
of the NORMALIZED model at scale `R = 2^k`. No marked DMS theorem on `B_{2^k}` is used.

Route, per `k` with `R = 2^k`:
* 4.1 normalization. `normField R hC hcirc` and `normCirc R hcirc` are the affine renormalization of the whole-plane GFF with
  `a = R`, `b = 0` (`WholePlaneGFFAffineInvariance`, derived in `S11v/Affine.lean`). They are a whole-plane GFF
  (`isWholePlaneGFF_normalized`, no input). The LQG measure of the normalized field is
  `normMeasure γ μ hcirc k ω = e^{-γ C_k(ω)} · zoomMeasure (μ ω) k`, with `C_k = hcirc ω R 0 + Q log R`. Its limit property
  comes from the Proposed input `LQGMeasureCoordChange` (`Proposed/LQG.lean`, pending source-check) and the constant
  shift `isLQGLimit_add_const` (proved here).
* 4.2 scale transfer. `hzoom_all_of_unit_models`: the constants are `a = e^{-γ C_k}` and `b = B⁻¹`, where `B` is the metric
  constant of the zoom.
* 4.3 unit ball. The unit-ball frequency statement of every normalized model is the hypothesis `UnitBallFrequencyModelsStmt`.
  It is NOT proved here: it is where the frozen `DMSLemmaA10WholePlaneMarked` and the unit-scale hFit/hCov/hFdef argument
  enter (see the report).
* The metric normalization (Fact 2.2 III-IV for the renormalized field) is `ZoomMetricNormStmt`, proved as
  `zoomMetricNormStmt_of_isLQGMetricOfField` from the axioms III, IV of `IsLQGMetric` (no hypothesis).
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

/-- **LQG measure of the normalized field (measure side).** `normMeasure γ μ hcirc k ω` is
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

/-- **Metric normalization at every scale** (proved for `Ω : Type` as `zoomMetricNormStmt_of_isLQGMetricOfField`). For every `k`, the renormalized field `normField (2^k) hC hcirc`
has an LQG metric `Dk` whose zoom relation holds: `zoomMetric (D ω) k = B · Dk ω` with `B > 0` almost surely. This is Fact 2.2
III-IV (weyl scaling and coordinate change of the metric, paper lines 432-457) for the renormalized field. -/
def ZoomMetricNormStmt (P : Measure Ω) (γ ξ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) : Prop :=
  ∀ k : ℕ, ∃ Dk : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ 0 (normField ((2 : ℝ) ^ k) hC hcirc) Dk ∧
    ∀ᵐ ω ∂P, ∃ B : ℝ, 0 < B ∧ ∀ x y, zoomMetric (D ω) k x y = B * Dk ω x y

/-- **Every `hzoom(k)`, from the unit-ball frequency of the normalized models.** For each `k`, almost surely
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

/-- **The composite consumed by `hphys` (with `hphys_of_zoom_const_family`).** The unit-ball frequency of the
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

/-! ### `ZoomMetricNormStmt`, proved from the axioms III and IV of `IsLQGMetric` (Fact 2.2 III-IV)

The renormalized pairing is `normField R hC hcirc ω = addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => -hcirc R 0)`.
Its LQG metric is the metric `𝔇` of `IsLQGMetric` evaluated at it. Axiom III gives the Weyl scaling by constants, and
`weylScaling_const` turns the constant into the factor `e^{ξ c}`; axiom IV (`coordChange`) gives the zoom. The universe of
`Ω` is `Type` here, as in `IsLQGMetric`. -/

/-- Pairing with the zero function is the identity: `addFunPairing T 0 = T`. -/
lemma addFunPairing_fun_zero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => (0 : ℝ)) = T := by
  funext φ
  simp [addFunPairing]

/-- **Weyl scaling by a constant** (Fact 2.2 III, line 445; GM21 (1.8)). `weylScaling D ξ c = e^{ξ c} · weylScaling D ξ 0`:
the integrand is the constant `e^{ξ c}`, the integral over `[0, T]` is `e^{ξ c} T`, and the infimum over the paths commutes
with the finite positive factor. -/
lemma weylScaling_const (D : ℂ → ℂ → ℝ) (ξ c : ℝ) (u v : ℂ) :
    weylScaling D ξ (fun _ => c) u v =
      ENNReal.ofReal (Real.exp (ξ * c)) * weylScaling D ξ (fun _ => 0) u v := by
  have hpos : ENNReal.ofReal (Real.exp (ξ * c)) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  unfold weylScaling
  simp only [setLIntegral_const, Real.volume_Icc, sub_zero, mul_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul,
    ENNReal.mul_iInf_of_ne hpos ENNReal.ofReal_ne_top]

/-- Axiom III of `IsLQGMetric` for a whole-plane GFF `G` (zero shift): almost surely, for every continuous `f`, the metric of
`G + f` is the Weyl scaling `e^{ξ f}` of the metric of `G`. -/
lemma ae_weylScaling_of_isWholePlaneGFF {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇) {G : Ω₀ → (ℂ → ℝ) → ℝ}
    {hcirc : Ω₀ → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P G hcirc) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v : ℂ,
      ENNReal.ofReal (𝔇 (addFunPairing (G ω) f) u v) = weylScaling (𝔇 (G ω)) ξ f u v := by
  have h := (hM.satisfiesLQGMetricAxioms Ω₀ P G hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)).ae_weylScaling
  simpa only [addFunPairing_fun_zero] using h

/-- The coordinate-change constants of axiom IV and of `normField` at scale `R > 0`: the pullback of `hC ω` by the
constant `lqgQ γ log R` is the renormalized pairing `normField R hC hcirc ω` shifted by `lqgQ γ log R + hcirc R 0`. -/
lemma addFunPairing_affine_eq_normField {Ω₀ : Type} {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ}
    (γ : ℝ) {R : ℝ} (hR : 0 < R) (ω : Ω₀) :
    addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => lqgQ γ * Real.log R) =
      addFunPairing (normField R hC hcirc ω) (fun _ => lqgQ γ * Real.log R + hcirc ω R 0) := by
  funext φ
  simp only [addFunPairing, affinePullbackPairing, normField, Complex.norm_real, Real.norm_of_nonneg hR.le,
    integral_const_mul]
  ring

/-- **Metric normalization at one scale** (Fact 2.2 III-IV for the renormalized field). For `R > 0` and `P`-a.e. `ω`, the
zoomed metric `(x, y) ↦ D ω (R x, R y)` is `e^{ξ c}` times the Weyl scaling of the metric of `normField R hC hcirc ω`,
with `c = lqgQ γ log R + hcirc R 0`. -/
lemma zoom_metric_identity {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇)
    {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ} {D : Ω₀ → ℂ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hDae : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun _ => 0) u v)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∃ B : ℝ, 0 < B ∧ ∀ x y : ℂ,
      (1 : ℝ) * D ω ((R : ℂ) * x) ((R : ℂ) * y) =
        B * (weylScaling (𝔇 (normField R hC hcirc ω)) ξ (fun _ => 0) x y).toReal := by
  have hWC := ae_weylScaling_of_isWholePlaneGFF hM hG
  have hWN := ae_weylScaling_of_isWholePlaneGFF hM (isWholePlaneGFF_normalized hG hR.ne')
  have hIV := (hM.satisfiesLQGMetricAxioms Ω₀ P hC hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)).coordChange R hR 0
  filter_upwards [hDae, hWC, hWN, hIV] with ω hD hWCω hWNω hIVω
  refine ⟨Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)), Real.exp_pos _, fun x y => ?_⟩
  simp only [addFunPairing_fun_zero, add_zero,
    addFunPairing_affine_eq_normField (hC := hC) (hcirc := hcirc) γ hR ω] at hIVω
  have hnn : 0 ≤ D ω ((R : ℂ) * x) ((R : ℂ) * y) := (hD _ _).1
  have h1 := (hD ((R : ℂ) * x) ((R : ℂ) * y)).2
  have h2 := hWCω (fun _ => 0) continuous_const ((R : ℂ) * x) ((R : ℂ) * y)
  simp only [addFunPairing_fun_zero] at h2
  have h3 := hIVω x y
  have h4 := hWNω (fun _ => lqgQ γ * Real.log R + hcirc ω R 0) continuous_const x y
  rw [weylScaling_const] at h4
  calc (1 : ℝ) * D ω ((R : ℂ) * x) ((R : ℂ) * y)
      = (ENNReal.ofReal (D ω ((R : ℂ) * x) ((R : ℂ) * y))).toReal := by
        rw [ENNReal.toReal_ofReal hnn, one_mul]
    _ = (weylScaling (𝔇 (hC ω)) ξ (fun _ => 0) ((R : ℂ) * x) ((R : ℂ) * y)).toReal := by rw [h1]
    _ = (ENNReal.ofReal (𝔇 (hC ω) ((R : ℂ) * x) ((R : ℂ) * y))).toReal := by rw [h2]
    _ = (ENNReal.ofReal (𝔇 (addFunPairing (normField R hC hcirc ω)
          (fun _ => lqgQ γ * Real.log R + hcirc ω R 0)) x y)).toReal := by rw [h3]
    _ = (ENNReal.ofReal (Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0))) *
          weylScaling (𝔇 (normField R hC hcirc ω)) ξ (fun _ => 0) x y).toReal := by rw [h4]
    _ = Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)) *
          (weylScaling (𝔇 (normField R hC hcirc ω)) ξ (fun _ => 0) x y).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- **`ZoomMetricNormStmt`, proved.** Let `hC` be a whole-plane GFF with LQG metric `D` (`IsLQGMetricOfField`, `α₀ = 0`). For
each `k`, the renormalized field `normField (2^k) hC hcirc` has the LQG metric `Dk ω x y = (weylScaling (𝔇 (normField ω)) ξ 0 x y).toReal`
(`𝔇` the metric of `IsLQGMetric` of `D`), and the zoom of `D` at scale `2^k` is a.s. a positive constant times `Dk`. Only
axioms III and IV of `IsLQGMetric` are used, together with `isWholePlaneGFF_normalized`. Probability spaces in `Type`, as
`IsLQGMetric` quantifies over them. -/
theorem zoomMetricNormStmt_of_isLQGMetricOfField {Ω₀ : Type} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ : ℝ}
    {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ} {D : Ω₀ → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ 0 hC D) :
    ZoomMetricNormStmt P γ ξ hC hcirc D := by
  obtain ⟨𝔇, hM, hDae⟩ := hD
  have hDae' : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun _ => 0) u v := by
    filter_upwards [hDae] with ω hω
    simpa only [neg_zero, zero_mul] using hω
  intro k
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  refine ⟨fun ω x y => (weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ (fun _ => 0) x y).toReal,
    ⟨𝔇, hM, ?_⟩, zoom_metric_identity hM hG hDae' hR⟩
  filter_upwards [ae_weylScaling_of_isWholePlaneGFF hM (isWholePlaneGFF_normalized hG hR.ne')] with ω hω
  intro u v
  have hfin : weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ (fun _ => 0) u v ≠ ⊤ := by
    rw [← hω (fun _ => 0) continuous_const u v, addFunPairing_fun_zero]
    exact ENNReal.ofReal_ne_top
  simp only [neg_zero, zero_mul]
  exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin⟩

end HarmonicBalls.FirstPassS11iHzoom
