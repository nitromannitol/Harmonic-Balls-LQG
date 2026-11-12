import HarmonicBalls.FirstPass.Phase2.Step8OriginFrequency

/-!
# Step 8 of Lemma 11.13: the certificate frequency at the origin for one fixed LQG metric

Fix an LQG metric `𝔇₀` (`IsLQGMetric γ ξ 𝔇₀`). Let `E` be a coding event on the field modulo constants in `B_7(0)`
that agrees almost surely with the certificate event at radius `1` about `0`, in every whole-plane model of the
insertion-`γ` field `h^γ = h^ℂ - γ log|·|` with its LQG measure and with the metric `D_h = e^{ξ f} · 𝔇₀(h^ℂ)`,
`f = -γ log|·|` (the Weyl scaling of `𝔇₀`). Then in every such model, almost surely, the frequency of the radii `2^{-n}`,
`n ∈ [N+1, 2N]`, at which the certificate event about `0` occurs tends to `P[h^γ|_{B_7} ∈ E]` (paper, Lemma 11.13,
Step 8, the frequency of eq. (16) at the root).

This is the form of `ae_tendsto_certificate_origin_frequency` (`Phase2/Step8OriginFrequency.lean`) for one fixed LQG
metric. The seed event of Lemma 11.12 for a fixed metric (`pinchLocalCertificate_seed_fixedMetric`,
`Phase2/Step8SeedFixedMetric.lean`) satisfies the hypothesis of this form without the uniqueness of the LQG metric
(GM21), whereas the hypothesis of the form for all metrics at once is produced only through that uniqueness.

Route. The half-scale pullback keeps the metric `𝔇₀`: the metric of the pulled-back model is
`D̃ ω u v = e^{-ξ c_ω} D ω (u/2) (v/2)`, which is again the Weyl scaling of `𝔇₀` at the pulled-back field
(`ae_fixedMetric_affinePullback`, the proof of `ae_isLQGMetricOfField_affinePullback` with the metric fixed). The
induction on `n` and Birkhoff's theorem for the ergodic dilation are then those of the form for all metrics.
-/

namespace HarmonicBalls.FirstPassPhase2Step8OriginFrequencyFixedMetric

open MeasureTheory Filter Topology Set Metric
open HarmonicBalls.FirstPassPhase2Step8OriginFrequency

/-- **Metric half of the B1 transfer for a fixed LQG metric.** For a whole-plane GFF model (`Ω : Type`) and an LQG
metric `𝔇₀`, if `D` is almost surely the Weyl scaling of `𝔇₀ (h^ℂ)` by `-α log|·|`, then
`D̃ ω u v = e^{-ξ c_ω} D ω (u/2) (v/2)`, with `c_ω = h^ℂ_{1/2}(0) - α log(1/2) + Q log(1/2)`, is almost surely the Weyl
scaling of `𝔇₀` at the pulled-back pairing `normDilatePairing (hC ω) (h^ℂ_{1/2}(0)) (1/2)` by `-α log|·|`: the same
metric `𝔇₀` serves the pulled-back model. -/
theorem ae_fixedMetric_affinePullback {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ ξ 𝔇₀) {D : Ω → ℂ → ℂ → ℝ}
    (hDae : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v) :
    ∀ᵐ ω ∂P, ∀ u v,
      0 ≤ Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
        * D ω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v) ∧
      ENNReal.ofReal (Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
        * D ω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)) =
        weylScaling (𝔇₀ (normDilatePairing (hC ω) (hcirc ω (1 / 2) 0) (1 / 2))) ξ
          (fun x => -α * Real.log ‖x‖) u v := by
  have hc : Measurable (fun ω => hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)) :=
    (hG.measurable_circle (1 / 2) 0 (by norm_num)).add_const _
  filter_upwards [hDae, ae_weylScaling_affinePullback_background hG 𝔇₀ h𝔇₀ (R := 1 / 2) (by norm_num)
    (fun ω => hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)) hc α] with ω hω hW
  have hP : addFunPairing (affinePullbackPairing (hC ω) (1 / 2) 0)
      (fun _ => lqgQ γ * Real.log (1 / 2) - (hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)))
      = normDilatePairing (hC ω) (hcirc ω (1 / 2) 0) (1 / 2) := by
    rw [normDilatePairing_eq_addFunPairing]
    congr 1
    funext x
    ring
  have hexp : -(ξ * ((hcirc ω (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)) - α * Real.log (1 / 2)))
      = -(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))) := by
    have h0 : fieldCircleAverage α (hcirc ω) (1 / 2) 0 = hcirc ω (1 / 2) 0 - α * Real.log (1 / 2) := by
      unfold fieldCircleAverage
      rw [circleAverage_log_norm_zero (by norm_num)]
    rw [h0]
    ring
  rw [hP] at hW
  intro u v
  refine ⟨mul_nonneg (Real.exp_nonneg _) (hω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)).1, ?_⟩
  rw [hW u v, ENNReal.ofReal_mul (Real.exp_nonneg _),
    (hω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)).2, hexp]

/-- **Certificate at radius `2^{-n}` as a dilation event, for a fixed LQG metric.** If the canonical field of `h^γ` lies
in `S` exactly when the certificate event at radius `1` about `0` occurs, almost surely in every insertion-`γ` model whose
metric is the Weyl scaling of `𝔇₀`, then for every `n` the same holds with `dilOp^[n]` of the canonical field and the
certificate event at radius `2^{-n}`. -/
theorem ae_iterate_mem_iff_certificate_fixedMetric {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ ξ 𝔇₀)
    {S : Set (ModConstTestPairings (univ : Set ℂ))} (hS : MeasurableSet S)
    (h0 : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (alphaCanon γ hC ω ∈ S ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0)) (n : ℕ) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (dilOp^[n] (alphaCanon γ hC ω) ∈ S ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) 0) := by
  induction n with
  | zero =>
    intro Ω _ P hC hcirc μ D hG hμ hD
    simpa using h0 Ω P hC hcirc μ D hG hμ hD
  | succ n ih =>
    intro Ω _ P hC hcirc μ D hG hμ hD
    have hG' := isWholePlaneGFF_affinePullback hG (wholePlaneGFFAffineInvariance_derived P hC hcirc)
    have hμ' := ae_isLQGMeasureOfField_affinePullback P hγ hG hμ
    have hD' := ae_fixedMetric_affinePullback P hG h𝔇₀ hD
    have hih := ih Ω P _ _ _
      (fun ω u v => Real.exp (-(ξ * (fieldCircleAverage γ (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
        * D ω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)) hG' hμ' hD'
    have hco := coordAe_mem_iff (P := P) (X := fun ω => dilOp (alphaCanon γ hC ω))
      (Y := fun ω => alphaCanon γ (fun ω' => normDilatePairing (hC ω') (hcirc ω' (1 / 2) 0) (1 / 2)) ω)
      (fun i => ae_dilOp_alphaCanon_apply_eq hG γ (fun ω => hcirc ω (1 / 2) 0) i)
      ((measurable_dilOp.iterate n) hS)
    have hr : (1 / 2 : ℝ) * (2 : ℝ)⁻¹ ^ n = (2 : ℝ)⁻¹ ^ (n + 1) := by
      rw [pow_succ]
      ring
    filter_upwards [hih, hco] with ω h1 h2
    rw [Function.iterate_succ_apply]
    refine (h2.trans h1).trans ((FirstPassS11iCertDilate.certificateEvent_dilate_iff (μ ω) (D ω) Ostar U V W T Q' Q
      η M ((2 : ℝ)⁻¹ ^ n) 0 (by norm_num : (0 : ℝ) < 1 / 2) (Real.exp_pos _) (Real.exp_pos _)).trans ?_)
    rw [mul_zero, hr]

/-- **Certificate frequency at the origin at insertion `γ`, for a fixed LQG metric (Lemma 11.13, Step 8).** Let `𝔇₀`
be an LQG metric and `E` a measurable coding event that agrees almost surely with the certificate event at radius `1`
about `0` in every insertion-`γ` model whose metric is the Weyl scaling of `𝔇₀` by `-γ log|·|`. Then in every such model,
almost surely, the window frequency of the certificate events at the radii `2^{-n}` about `0` tends to the probability
of `E`. -/
theorem ae_tendsto_certificate_origin_frequency_fixedMetric {γ ξ : ℝ} (hγ : 0 < γ) {Ostar U V W T Q' Q : Set ℂ}
    {η M : ℝ} {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : HarmonicBalls.IsLQGMetric γ ξ 𝔇₀)
    {E : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M 1 0))
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ γ hcirc μ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇₀ (hC ω)) ξ (fun x => -γ * Real.log ‖x‖) u v) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) 0}.ncard : ℕ) : ℝ)
        / (N : ℝ)) atTop (𝓝 (P {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E}).toReal) := by
  classical
  have : IsProbabilityMeasure P := FirstPassS11af.isProbabilityMeasure_of_isWholePlaneGFF hG
  set S : Set (ModConstTestPairings (univ : Set ℂ)) := canonRestrict (ball (0 : ℂ) 7) ⁻¹' E with hSdef
  have hS : MeasurableSet S := measurable_canonRestrict _ hE
  have hall := ae_iterate_mem_iff_certificate_fixedMetric (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T)
    (Q' := Q') (Q := Q) (η := η) (M := M) hγ h𝔇₀ hS
    (fun Ω _ P hC hcirc μ D hG hμ hD => hEq Ω P hC hcirc μ D hG hμ hD)
  have hn := ae_all_iff.2 fun n => hall n Ω P hC hcirc μ D hG hμ hD
  have hfreq := ae_alpha_canonical_window_frequency hG birkhoffPointwiseErgodic_derived γ hS
  have hset : {ω | alphaCanon γ hC ω ∈ S} = {ω | localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E} := rfl
  rw [hset] at hfreq
  filter_upwards [hfreq, hn] with ω hω hnω
  refine hω.congr fun N => ?_
  congr 1
  have hfin : {n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
      FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M ((2 : ℝ)⁻¹ ^ n) 0} =
      ↑((Finset.Icc (N + 1) (2 * N)).filter (fun n => dilOp^[n] (alphaCanon γ hC ω) ∈ S)) := by
    ext n
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq, hnω n, and_assoc]
  rw [hfin, Set.ncard_coe_finset]
  simp only [Set.indicator_apply, Finset.sum_boole]

end HarmonicBalls.FirstPassPhase2Step8OriginFrequencyFixedMetric
