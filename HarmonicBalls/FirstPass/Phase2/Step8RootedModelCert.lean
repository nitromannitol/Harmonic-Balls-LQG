import HarmonicBalls.FirstPass.Phase2.Step8HrefOfModel
import HarmonicBalls.FirstPass.Phase2.CampbellTranslate
import HarmonicBalls.FirstPass.Phase2.LQGMeasureExistenceDerived
import HarmonicBalls.FirstPass.Phase2.LengthUnivDerived
import HarmonicBalls.FirstPass.Phase2.WeylCompositionOuterDerived
import HarmonicBalls.FirstPass.Phase2.GFFExistsDerived2
import HarmonicBalls.FirstPass.S11i.Final11_13
import HarmonicBalls.FirstPass.S11r.RootedTranslate
import HarmonicBalls.FirstPass.S11r.RootedLocalIdent
import HarmonicBalls.FirstPass.S11r.RootedHrefGlobal

/-!
# Lemma 11.13, Step 8: the model certificate at the root for the ball decoders

This file proves the statement `RootedModelCertificateStmt` (`Phase2/Step8HrefOfModel.lean`) for the ball decoders
`ballKernel`, `ballMetric` of a valid ball, in every whole-plane model and for every LQG metric `𝔇`, and with it the
named field `hHref` of `insertionZeroUnit_of_href` from the seed of Lemma 11.12 alone.

Fix a root `z` of the ball. The model at `z` is the field `h^ℂ(· + z) - h^ℂ_1(z)` with the log singularity of
insertion `γ` at `0`: its LQG measure `ν` (which exists, `lqgMeasureExistence_derived`) and its LQG metric
`centredWeylMetric`.
* Measure. The rooted LQG measure is the translate `e^{γ h_1(z)} ν(· - z)`, weighted by `exp(γ² log max(1,|·|))`
  (`ae_isLQGLimit_rootedMax_of_translated`). The regularized measures transform exactly under the translation
  (`IsLQGLimit.translate`), so no coordinate change rule is used. By the kernel clause of `LocalMeasureKernelStmt`, the
  decoded kernel near `z` is a positive multiple of this translate (`map_sub_restrict_closedBall_eq`).
* Metric. By clause (20) of `LocalMetricReplacementStmt` the decoded metric is a positive multiple of the internal
  metric of the rooted Weyl metric on the decoder disc, which at translated points is `e^{ξ h_1(z)}` times the internal
  metric of `centredWeylMetric` (`ae_rootedWeylMetric_internalMetric_translate`, Fact 2.2 of Bou-Rabee-Gwynne).
* The no-shortcut comparison (`ae_eventual_certificateEvent_decoded`) and the translation of certificate events
  (`certificateEvent_translate_iff`) give the eventual equality of the certificates.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassPhase2Step8RootedModelCert

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassPhase2Step8HrefOfModel
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
open HarmonicBalls.FirstPassS11rRootedBallMetric HarmonicBalls.FirstPassS11rRootedHrefGlobal

/-- **The rooted LQG measure as a translate, without the coordinate change rule.** If `ν` is the LQG measure (insertion
`γ`) of the field translated by `z` and normalized at `z`, then almost surely `e^{γ h_1(z)} ν(· - z)` is the vague limit
of the regularized measures of the rooted circle averages `h_ε(·) - γ (log |· - z|)_ε`. -/
theorem ae_isLQGLimit_rooted_of_translated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (z : ℂ)
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ (translatedCircle hcirc z) ν) :
    ∀ᵐ ω ∂P, IsLQGLimit γ (rootedCircleAverage 0 γ z (hcirc ω))
      (ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z)) := by
  have hGT := isWholePlaneGFF_translate hG z
  have hcont : ∀ᵐ ω ∂P, ∀ k : ℕ,
      Continuous (fieldCircleAverage γ (translatedCircle hcirc z ω) (dyadicScale k)) :=
    ae_all_iff.mpr fun k => hGT.ae_continuous_fieldCircleAverage γ (dyadicScale_pos k)
  filter_upwards [hν, hcont] with ω hω hωc
  have shifted := IsLQGLimit.translate (fun k => (hωc k).measurable) hω (-z) (-(hcirc ω 1 z))
  have e1 : rootedCircleAverage 0 γ z (hcirc ω) =
      fun r x => fieldCircleAverage γ (translatedCircle hcirc z ω) r (x + -z) - -(hcirc ω 1 z) := by
    funext e w
    rw [← sub_eq_add_neg]
    exact rootedCircleAverage_zero_eq γ (hcirc ω) (translatedCircle hcirc z ω) z (fun r x => rfl) e w
  have e2 : ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z) =
      ENNReal.ofReal (Real.exp (-(γ * -(hcirc ω 1 z)))) • (ν ω).map (fun x => x - -z) := by
    simp only [sub_neg_eq_add, mul_neg, neg_neg]
  rw [e1, e2]
  exact shifted

/-- **The rooted LQG measure with the `γ log max(1,|·|)` normalization, without the coordinate change rule.** The same
measure as `ae_isLQGLimit_rootedMax` (`S11r/RootedLocalIdent.lean`), whose binder `hCC` is not needed: the field is
only translated. -/
theorem ae_isLQGLimit_rootedMax_of_translated {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (z : ℂ)
    {ν : Ω → Measure ℂ} (hν : IsLQGMeasureOfField P γ γ (translatedCircle hcirc z) ν) :
    IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage 0 (hcirc ω))
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)))
      (fun ω => (ENNReal.ofReal (Real.exp (γ * hcirc ω 1 z)) • (ν ω).map (fun x => x + z)).withDensity fun w =>
        ENNReal.ofReal (Real.exp (γ * (γ * Real.log (max 1 ‖w‖))))) := by
  have hlim := ae_isLQGLimit_rooted_of_translated hG z hν
  have hcont : ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (fieldCircleAverage 0 (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr (fun n => hG.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n))
  filter_upwards [hlim, hcont] with ω hω hωc
  have hW := Section6.isLQGLimit_addCircleAverage hω
    (fun n => continuous_rootedCircleAverage_of_field (dyadicScale_pos n) (hωc n))
    (fun w => γ * Real.log (max 1 ‖w‖)) (continuous_gamma_log_max_one γ)
  have heq : addCircleAverage (rootedCircleAverage 0 γ z (hcirc ω)) (fun w => γ * Real.log (max 1 ‖w‖)) =
      addCircleAverage (fieldCircleAverage 0 (hcirc ω))
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) := by
    funext r x
    simp only [addCircleAverage, rootedCircleAverage]
    have hL : CircleIntegrable (fun w : ℂ => Real.log ‖w - z‖) x r := circleIntegrable_log_norm_sub_const r
    have hV : CircleIntegrable (fun w : ℂ => γ * Real.log (max 1 ‖w‖)) x r :=
      (continuous_gamma_log_max_one γ).continuousOn.circleIntegrable'
    have hA : CircleIntegrable (fun w : ℂ => -γ * Real.log ‖w - z‖) x r := hL.const_mul (-γ)
    have hscal : Real.circleAverage (fun w : ℂ => -γ * Real.log ‖w - z‖) x r =
        -γ * Real.circleAverage (fun w : ℂ => Real.log ‖w - z‖) x r := by
      have h1 : (fun w : ℂ => -γ * Real.log ‖w - z‖) = fun w => (-γ) • Real.log ‖w - z‖ := by
        funext w
        simp [smul_eq_mul]
      rw [h1, Real.circleAverage_fun_smul, smul_eq_mul]
    rw [show (fun w : ℂ => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) =
        fun w => (-γ * Real.log ‖w - z‖) + (γ * Real.log (max 1 ‖w‖)) from rfl,
      Real.circleAverage_fun_add hA hV, hscal]
    ring
  rw [heq] at hW
  exact hW

/-- **The decoded kernel near the root, pulled back to `0`.** If on a window `D ⊆ B₁(0)` the kernel `κ'` is `a` times the
weighted translate `(e^c ν(· - z)) · exp(γ² log max(1,|·|))`, and `B̄_s(z) ⊆ D`, then on `B̄_s(0)` the pullback
`κ'(· + z)` is `a e^c ν`. -/
theorem map_sub_restrict_closedBall_eq {κ' ν : Measure ℂ} {z : ℂ} {D : Set ℂ} (hD : MeasurableSet D)
    (hD1 : D ⊆ ball (0 : ℂ) 1) {γ a c : ℝ} (ha : 0 < a)
    (h : κ'.restrict D = ENNReal.ofReal a • ((ENNReal.ofReal (Real.exp c) • ν.map (fun x => x + z)).withDensity
      fun w => ENNReal.ofReal (Real.exp (γ * (γ * Real.log (max 1 ‖w‖))))).restrict D)
    {s : ℝ} (hs : closedBall z s ⊆ D) :
    (κ'.map (fun w => w - z)).restrict (closedBall 0 s) =
      (ENNReal.ofReal (a * Real.exp c) • ν).restrict (closedBall 0 s) := by
  have hg : ∀ x ∈ D, (fun w : ℂ => γ * Real.log (max 1 ‖w‖)) x = 0 := by
    intro x hx
    have hx1 : ‖x‖ < 1 := by simpa using hD1 hx
    simp only [max_eq_left hx1.le, Real.log_one, mul_zero]
  ext t ht
  have hB : MeasurableSet (t ∩ closedBall (0 : ℂ) s) := ht.inter measurableSet_closedBall
  have hBD : (fun w => w - z) ⁻¹' (t ∩ closedBall (0 : ℂ) s) ⊆ D := by
    intro w hw
    apply hs
    have h2 := hw.2
    simp only [mem_closedBall, dist_zero_right] at h2
    simpa [mem_closedBall, dist_eq_norm] using h2
  rw [Measure.restrict_apply ht, Measure.restrict_apply ht, Measure.map_apply (continuous_sub_right z).measurable hB,
    kappa_preimage_eq (g := fun w : ℂ => γ * Real.log (max 1 ‖w‖)) hD hg γ h hB hBD, Measure.smul_apply,
    smul_eq_mul, ENNReal.ofReal_mul ha.le, mul_assoc]

/-- The ball metric is nonnegative on the decoder disc: it is either a length metric on the disc or the Euclidean
distance. -/
theorem ballMetric_nonneg {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ)
    (ℓ : FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p)) {x y : ℂ}
    (hx : x ∈ ball (ballCen p) (2 * ballRad p)) (hy : y ∈ ball (ballCen p) (2 * ballRad p)) :
    0 ≤ ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p ℓ x y := by
  unfold ballMetric
  split_ifs with h
  · exact h.nonneg hx hy
  · exact dist_nonneg

/-- The centred Weyl metric of the translated field is an LQG metric (insertion `γ`) of that field and is almost surely a
Euclidean length metric (Fact 2.2 I, `hAx`). -/
theorem isLQGMetricOfField_centredWeylMetric (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) (z : ℂ) :
    IsLQGMetricOfField P γ ξ γ (translatedPairing hC hcirc z) (centredWeylMetric 𝔇 ξ γ hC hcirc z) ∧
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (centredWeylMetric 𝔇 ξ γ hC hcirc z ω) := by
  have hfin := hAx Ω P γ ξ γ (translatedPairing hC hcirc z) (translatedCircle hcirc z)
    (isWholePlaneGFF_translate hG z) hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2) 𝔇 h𝔇
  refine ⟨⟨𝔇, h𝔇, ?_⟩, ?_⟩
  · filter_upwards [hfin.1] with ω hω
    intro u v
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hω.1 u v).ne⟩
  · filter_upwards [hfin.1] with ω hω
    exact hω.2

/-- **The model certificate at the root for the ball decoders (Lemma 11.13, Step 8).** In a whole-plane model, for an
LQG metric `𝔇` and a valid ball `p`, at almost every root `z` of the ball the LQG measure `ν` and the centred Weyl metric
of the field translated by `z` (insertion `γ`) have certificates at radii `2⁻ⁿ` about `0` that eventually agree, almost
surely, with the decoded local certificates (decoders `ballKernel`, `ballMetric`) of the Campbell reference observation
at `z`. Inputs: the frozen decoder statements `hK`, `hR`, the rooted continuity `hfr` and Fact 2.2 (`hAx`). -/
theorem rootedModelCertificate_ballDecoders {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇) (p : ℚ × ℚ × ℚ) (hp : ValidBall p)
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7) :
    RootedModelCertificateStmt P γ (lqgXi γ) hC hcirc (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)
      (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) Ostar U V W T Q' Q η M := by
  obtain ⟨-, hcl, hout, h0⟩ := validBall_facts hp
  have hXi : LQGMetricExponentPositive :=
    FirstPassS11iFinal11_13.lqgMetricExponentPositive_derived wholePlaneGFFExistsFrozen_derived'.{0}
  have hκ := ballKernel_clause hγ0 hγ2 hK p hp 0 (lqgQ_pos hγ0) Ω P hC hcirc hG
  have hm := metricCont_clause20 hγ0 hγ2 hR 𝔇 h𝔇 p hp 0 (lqgQ_pos hγ0) Ω P hC hcirc hG
  have hbm := ae_ballMetric_decodedRoot_eq (α₀ := 0) hG hfr hγ0 hγ2 (lqgQ_pos hγ0) hR h𝔇 p hp
  filter_upwards [hκ, hm, hbm, ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball]
    with z hzκ hzm hzb hz
  have hzB : z ∈ ball (ballCen p) (2 * ballRad p) := hcl (ball_subset_closedBall hz)
  have hz0 : z ≠ 0 := fun h => h0 (h ▸ ball_subset_closedBall hzB)
  have hB1 : ball (ballCen p) (2 * ballRad p) ⊆ ball (0 : ℂ) 1 := ball_subset_closedBall.trans hout
  obtain ⟨ν, hν⟩ := lqgMeasureExistence_derived P γ γ (translatedPairing hC hcirc z) (translatedCircle hcirc z)
    (isWholePlaneGFF_translate hG z) hγ0 hγ2 (gamma_lt_lqgQ hγ0 hγ2)
  obtain ⟨hDT, hDu⟩ := isLQGMetricOfField_centredWeylMetric hAx hγ0 hγ2 hG h𝔇 z
  refine ⟨ν, centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z, hν, hDT, ?_⟩
  obtain ⟨r₀, hr₀, hr₀B⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ closedBall z r₀ ⊆ ball (ballCen p) (2 * ballRad p) := by
    obtain ⟨ε, hε, hεB⟩ := Metric.isOpen_iff.1 isOpen_ball z hzB
    exact ⟨ε / 2, half_pos hε, (closedBall_subset_ball (half_lt_self hε)).trans hεB⟩
  have hmem : ∀ u ∈ closedBall (0 : ℂ) r₀, u + z ∈ ball (ballCen p) (2 * ballRad p) := fun u hu =>
    hr₀B (by simpa [mem_closedBall, dist_eq_norm] using hu)
  -- the decoded metric near the root
  have hT := ae_rootedWeylMetric_internalMetric_translate hγ0 hγ2 hout hG h𝔇 hXi hAx
    FirstPassS11iFinal11_13.lqgMetricSatisfiesAxiomsUnivFrozen_zero lqgMetricLengthUniv_derived.{0} hfr
    weylMetricCompositionContinuousOuter_derived hz0
  have hDecInt : ∀ᵐ ω ∂P, ∃ (W₀ : Set ℂ) (r β : ℝ), IsOpen W₀ ∧ (0 : ℂ) ∈ W₀ ∧ 0 < r ∧ 0 < β ∧
      ∀ x ∈ closedBall (0 : ℂ) r, ∀ y ∈ closedBall (0 : ℂ) r,
        ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 (x + z) (y + z) =
          β * (internalMetric (centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z ω) W₀ x y).toReal := by
    filter_upwards [hzm, hzb, hT] with ω hωm hωb hωT
    obtain ⟨b, hb, hbq⟩ := hωm
    refine ⟨(fun u => u + z) ⁻¹' ball (ballCen p) (2 * ballRad p), r₀, b * Real.exp (lqgXi γ * hcirc ω 1 z),
      isOpen_ball.preimage (continuous_id.add continuous_const), by simpa using hzB, hr₀,
      mul_pos hb (Real.exp_pos _), fun x hx y hy => ?_⟩
    have hq : (x + z, y + z) ∈ ball (ballCen p) (2 * ballRad p) ×ˢ ball (ballCen p) (2 * ballRad p) := ⟨hmem x hx, hmem y hy⟩
    have e1 : ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 (x + z) (y + z) =
        metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 ⟨(x + z, y + z), hq⟩ := by
      have h1 := congrFun (congrFun hωb (x + z)) (y + z)
      simp only [FirstPassS11at.decodedRootMetric] at h1
      rw [h1]
      simp only [FirstPassS11at.windowMetric, hq, ↓reduceDIte]
    have e2 : ENNReal.ofReal (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2
        ⟨(x + z, y + z), hq⟩) = ENNReal.ofReal b * (ENNReal.ofReal (Real.exp (lqgXi γ * hcirc ω 1 z)) *
          internalMetric (centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z ω) ((fun u => u + z) ⁻¹' ball (ballCen p) (2 * ballRad p)) x y) := by
      rw [hbq ⟨(x + z, y + z), hq⟩]
      congr 1
      exact hωT x y (hmem x hx) (hmem y hy)
    have hnn := ballMetric_nonneg hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2
      (hmem x hx) (hmem y hy)
    rw [← ENNReal.toReal_ofReal hnn, e1, e2, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hb.le,
      ENNReal.toReal_ofReal (Real.exp_pos _).le, mul_assoc]
  -- the decoded kernel near the root
  have hκz := hzκ _ (ae_isLQGLimit_rootedMax_of_translated hG z hν)
  have h7 : Tendsto (fun n : ℕ => 7 * certScale n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => certScale n) atTop (𝓝 0) := by
      simpa [certScale] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)
    simpa using h1.const_mul 7
  obtain ⟨n₁, hn₁⟩ := eventually_atTop.1 (h7.eventually (gt_mem_nhds hr₀))
  have hMass : ∀ᵐ ω ∂P, ∃ n₁ : ℕ, ∀ n ≥ n₁, ∃ a : ℝ, 0 < a ∧
      ((ballKernel hγ0 hγ2 hK p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2).map (fun w => w - z)).restrict
          (closedBall 0 (7 * certScale n)) =
        (ENNReal.ofReal a • ν ω).restrict (closedBall 0 (7 * certScale n)) := by
    filter_upwards [hκz] with ω hω
    obtain ⟨a, ha, hka⟩ := hω
    exact ⟨n₁, fun n hn => ⟨a * Real.exp (γ * hcirc ω 1 z), mul_pos ha (Real.exp_pos _),
      map_sub_restrict_closedBall_eq measurableSet_ball hB1 ha hka
        ((closedBall_subset_closedBall (hn₁ n hn).le).trans hr₀B)⟩⟩
  have hdec := FirstPassS11at.ae_eventual_certificateEvent_decoded (P := P)
    (fun ω => (ballKernel hγ0 hγ2 hK p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2).map (fun w => w - z)) ν
    (fun ω x y => ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2 (x + z) (y + z))
    (centredWeylMetric 𝔇 (lqgXi γ) γ hC hcirc z) Ostar U V W T Q' Q η M hCont hU hDu hDecInt hMass
  filter_upwards [hdec] with ω hω
  obtain ⟨n₀, hn₀⟩ := hω
  refine eventually_atTop.2 ⟨n₀, fun n hn => ?_⟩
  have htr := FirstPassS11aq.certificateEvent_translate_iff
    (ballKernel hγ0 hγ2 hK p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2)
    (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2) Ostar U V W T Q' Q η M
    (certScale n) 0 z
  rw [zero_add] at htr
  exact htr.symm.trans (hn₀ n hn)

/-- **The binder `hPhys` of `hHref_of_modelCertificate`**, for a buffered pinch geometry: the model certificate at the
root for the ball decoders, in every whole-plane model, for every LQG metric and every valid ball. -/
theorem hPhys_ballDecoders {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0}) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ)
      (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          RootedModelCertificateStmt P γ (lqgXi γ) hC' hcirc' (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)
            (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M := by
  obtain ⟨-, -, -, hCont⟩ := FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo
  intro Ω _ P _ hC' hcirc' 𝔇 h𝔇 hG p hp
  exact rootedModelCertificate_ballDecoders hγ0 hγ2 hK hR hfr hAx hG h𝔇 p hp hCont
    (hgeo.U_subset.trans (FirstPassS11ap.annulus_subset_closedBall' 0 1 2 7 (by norm_num)))

/-- **The named field `hHref` of `insertionZeroUnit_of_href` from the seed of Lemma 11.12.** The binder `hPhys` of
`hHref_of_modelCertificate` is `hPhys_ballDecoders`. Inputs besides the seed `hEq`: the frozen decoder statements `hK`,
`hR`, the rooted continuity `hfr` (all three binders of `insertionZeroUnit_of_href`) and Fact 2.2 (`hAx`). -/
theorem hHref_of_seed {γ δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0}) (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ → IsLQGMetricOfField P γ (lqgXi γ) γ hC D →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0)) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (q : ℝ),
      CommonProb.{0} γ E q →
      ∀ (hC' : Ω → (ℂ → ℝ) → ℝ) (hcirc' : Ω → ℝ → ℂ → ℝ) (μ' : Ω → Measure ℂ)
        (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇),
        HarmonicBalls.IsWholePlaneGFF P hC' hcirc' → HarmonicBalls.IsLQGMeasureOfField P γ 0 hcirc' μ' →
        ∀ p : ℚ × ℚ × ℚ, ValidBall p →
          ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
            campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC' ω) z ∉
              HarmonicBalls.ReferenceNullS11i.refBadWindowSet
                (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
                  (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q :=
  hHref_of_modelCertificate hγ0 hγ2 hK hR hE hEq (hPhys_ballDecoders hγ0 hγ2 hgeo hK hR hfr hAx)

end HarmonicBalls.FirstPassPhase2Step8RootedModelCert
