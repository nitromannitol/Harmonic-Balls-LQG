import HarmonicBalls.FirstPass.Phase2.LQGMetricAxiomsUniv
import HarmonicBalls.FirstPass.Phase2.Step8TransferK0Unrooted

/-!
# The Step 8 identity (Lemma 11.13) on probability spaces of every universe

The Step 8 chain of Lemma 11.13 was proved over probability spaces in `Type` only
(`step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms`, `Phase2/Step8TransferK0Unrooted.lean`),
because the axioms of an LQG metric (`IsLQGMetric`) are stated over `Type`. The theorem
`IsLQGMetric.satisfiesLQGMetricAxioms_univ` (`Phase2/LQGMetricAxiomsUniv.lean`) gives these axioms on probability spaces
of every universe. This file repeats the chain with that theorem, at universe `u`:

* the metric normalization at scale `R` of an insertion-`α` LQG metric (`zoom_metric_alpha_identity_univ`,
  `zoomMetricNormAlpha_of_isLQGMetricOfField_univ`, `zoomMetricNormAlpha0_stmt_univ`);
* the insertion transfer at unit scale (`disc_transfer_k0_of_normalizedMetric_univ`,
  `allModelsAt_insertion_of_zero_k0_of_normalizedMetric_univ`);
* route 1 from the unit scale to every scale (`allModelsAt_all_scales_of_scale_zero_univ`);
* the Step 8 identity from the event calibration and the metric field axioms
  (`step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ`).

The proofs are those of the universe-`0` statements, with `satisfiesLQGMetricAxioms_univ` in place of the field
`IsLQGMetric.satisfiesLQGMetricAxioms`.
-/

universe u

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iHzoom

open HarmonicBalls.FirstPassS11iStep8Zoom FirstPassS11i

/-- Axiom III of `IsLQGMetric` for a whole-plane GFF `G` on a probability space of any universe (zero shift): almost
surely, for every continuous `f`, the metric of `G + f` is the Weyl scaling `e^{ξ f}` of the metric of `G`. -/
lemma ae_weylScaling_of_isWholePlaneGFF_univ {Ω₀ : Type u} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇) {G : Ω₀ → (ℂ → ℝ) → ℝ}
    {hcirc : Ω₀ → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P G hcirc) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → ∀ u v : ℂ,
      ENNReal.ofReal (𝔇 (addFunPairing (G ω) f) u v) = weylScaling (𝔇 (G ω)) ξ f u v := by
  have h := (hM.satisfiesLQGMetricAxioms_univ Ω₀ P G hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)).ae_weylScaling
  simpa only [addFunPairing_fun_zero] using h

/-- The coordinate-change constants of axiom IV and of `normField` at scale `R > 0`, on a sample space of any
universe. -/
lemma addFunPairing_affine_eq_normField_univ {Ω₀ : Type u} {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ}
    (γ : ℝ) {R : ℝ} (hR : 0 < R) (ω : Ω₀) :
    addFunPairing (affinePullbackPairing (hC ω) R 0) (fun _ => lqgQ γ * Real.log R) =
      addFunPairing (normField R hC hcirc ω) (fun _ => lqgQ γ * Real.log R + hcirc ω R 0) := by
  funext φ
  simp only [addFunPairing, affinePullbackPairing, normField, Complex.norm_real, Real.norm_of_nonneg hR.le,
    integral_const_mul]
  ring

end HarmonicBalls.FirstPassS11iHzoom

namespace HarmonicBalls.FirstPassS11iZoomMetricAlpha0

open HarmonicBalls.FirstPassS11iHzoom HarmonicBalls.FirstPassS11iStep8PhysReduction
open HarmonicBalls.FirstPassS11iStep8Zoom

/-- **Metric normalization at one scale, insertion `α`, any universe.** For `R > 0`, almost surely the zoomed metric
`(x, y) ↦ D ω (R x, R y)` is `e^{ξ (h_R(0) + (Q - α) log R)}` times the Weyl scaling by `-α log |·|` of the metric of the
normalized field `normField R`. -/
theorem zoom_metric_alpha_identity_univ {Ω₀ : Type u} [MeasurableSpace Ω₀] {P : Measure Ω₀} {γ ξ α : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hM : IsLQGMetric γ ξ 𝔇)
    {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ} {D : Ω₀ → ℂ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hDae : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    {R : ℝ} (hR : 0 < R) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, ENNReal.ofReal (D ω ((R : ℂ) * x) ((R : ℂ) * y)) =
      ENNReal.ofReal (Real.exp (ξ * (hcirc ω R 0 + (lqgQ γ - α) * Real.log R))) *
        weylScaling (𝔇 (normField R hC hcirc ω)) ξ (fun x => -α * Real.log ‖x‖) x y := by
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hGN := isWholePlaneGFF_normalized hG hR.ne'
  have hWN := ae_weylScaling_of_isWholePlaneGFF_univ hM hGN
  have hIV := (hM.satisfiesLQGMetricAxioms_univ Ω₀ P hC hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)).coordChange R hR 0
  have hI0 := (hM.satisfiesLQGMetricAxioms_univ Ω₀ P hC hcirc (fun _ _ => (0 : ℝ)) hG
    (fun _ => continuous_const) (fun _ => measurable_const)).ae_isEuclideanLengthMetric
  have hIN := (hM.satisfiesLQGMetricAxioms_univ Ω₀ P (normField R hC hcirc) (normCirc R hcirc)
    (fun _ _ => (0 : ℝ)) hGN (fun _ => continuous_const) (fun _ => measurable_const)).ae_isEuclideanLengthMetric
  filter_upwards [hDae, hWN, hIV, hI0, hIN] with ω hDω hWNω hIVω hI0ω hINω
  simp only [addFunPairing_fun_zero] at hI0ω hINω
  simp only [addFunPairing_fun_zero, add_zero,
    addFunPairing_affine_eq_normField_univ (hC := hC) (hcirc := hcirc) γ hR ω] at hIVω
  -- The metric of `hC ω` at scale `R` is `e^{ξ c}` times the metric of the normalized field, `c = Q log R + h_R(0)`.
  have hc : ∀ a b : ℂ, 𝔇 (hC ω) ((R : ℂ) * a) ((R : ℂ) * b) =
      Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)) * 𝔇 (normField R hC hcirc ω) a b := by
    intro a b
    have hA := hWNω (fun _ => lqgQ γ * Real.log R + hcirc ω R 0) continuous_const a b
    rw [weylScaling_const] at hA
    have hB := hWNω (fun _ => (0 : ℝ)) continuous_const a b
    simp only [addFunPairing_fun_zero] at hB
    have hnn0 := isEuclideanLengthMetric_nonneg hI0ω ((R : ℂ) * a) ((R : ℂ) * b)
    have hnn1 := isEuclideanLengthMetric_nonneg hINω a b
    rw [← ENNReal.ofReal_eq_ofReal_iff hnn0 (mul_nonneg (Real.exp_pos _).le hnn1), hIVω a b, hA, ← hB,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  intro x y
  have hL := (hDω ((R : ℂ) * x) ((R : ℂ) * y)).2
  have hdil' : weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) ((R : ℂ) * x) ((R : ℂ) * y) =
      weylScaling (fun a b => 𝔇 (hC ω) (Homeomorph.mulLeft₀ (R : ℂ) hRc a) (Homeomorph.mulLeft₀ (R : ℂ) hRc b))
        ξ ((fun z => -α * Real.log ‖z‖) ∘ Homeomorph.mulLeft₀ (R : ℂ) hRc) x y :=
    (weylScaling_comp_homeomorph (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖)
      (Homeomorph.mulLeft₀ (R : ℂ) hRc) x y).symm
  have hfun : (fun a b => 𝔇 (hC ω) (Homeomorph.mulLeft₀ (R : ℂ) hRc a) (Homeomorph.mulLeft₀ (R : ℂ) hRc b)) =
      fun a b => Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)) * 𝔇 (normField R hC hcirc ω) a b :=
    funext fun a => funext fun b => hc a b
  have hcong : weylScaling (𝔇 (normField R hC hcirc ω)) ξ
      ((fun z => -α * Real.log ‖z‖) ∘ Homeomorph.mulLeft₀ (R : ℂ) hRc) x y =
      weylScaling (𝔇 (normField R hC hcirc ω)) ξ (fun z => -α * Real.log ‖z‖ + -α * Real.log R) x y := by
    refine weylScaling_congr_of_ne_zero hINω ξ _ _ (fun z hz => ?_) x y
    show -α * Real.log ‖(R : ℂ) * z‖ = -α * Real.log ‖z‖ + -α * Real.log R
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le,
      Real.log_mul hR.ne' (norm_ne_zero_iff.mpr hz)]
    ring
  have hexp : Real.exp (ξ * (lqgQ γ * Real.log R + hcirc ω R 0)) * Real.exp (ξ * (-α * Real.log R)) =
      Real.exp (ξ * (hcirc ω R 0 + (lqgQ γ - α) * Real.log R)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hL, hdil', hfun, IsEuclideanLengthMetric.weylScaling_const_mul hINω
    (Real.exp_pos (ξ * (lqgQ γ * Real.log R + hcirc ω R 0))), hcong,
    weylScaling_add_const, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos (ξ * (lqgQ γ * Real.log R + hcirc ω R 0))).le, hexp]

/-- **`ZoomMetricNormAlphaFor`, any universe.** For a whole-plane model and an LQG metric `D` of the insertion-`α`
field, the zoom of `D` at scale `2^k` is almost surely a positive constant times an insertion-`α` LQG metric of the
normalized field `normField (2^k)`. -/
theorem zoomMetricNormAlpha_of_isLQGMetricOfField_univ {Ω₀ : Type u} [MeasurableSpace Ω₀] {P : Measure Ω₀}
    {γ ξ α : ℝ}
    {hC : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc : Ω₀ → ℝ → ℂ → ℝ} {D : Ω₀ → ℂ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ZoomMetricNormAlphaFor P γ ξ α hC hcirc D := by
  obtain ⟨𝔇, hM, hDae⟩ := hD
  intro k
  have hR : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hid := zoom_metric_alpha_identity_univ hM hG hDae hR
  refine ⟨fun ω x y => (weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
      (fun x => -α * Real.log ‖x‖) x y).toReal, ⟨𝔇, hM, ?_⟩, ?_⟩
  · filter_upwards [hid] with ω hω
    intro u v
    have hfin : weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
        (fun x => -α * Real.log ‖x‖) u v ≠ ⊤ := by
      intro htop
      have h := hω u v
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at h
      exact ENNReal.ofReal_ne_top h
    exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin⟩
  · filter_upwards [hid, hDae] with ω hω hDω
    refine ⟨Real.exp (ξ * (hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α) * Real.log ((2 : ℝ) ^ k))),
      Real.exp_pos _, fun x y => ?_⟩
    have hfin : weylScaling (𝔇 (normField ((2 : ℝ) ^ k) hC hcirc ω)) ξ
        (fun x => -α * Real.log ‖x‖) x y ≠ ⊤ := by
      intro htop
      have h := hω x y
      rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at h
      exact ENNReal.ofReal_ne_top h
    have h := hω x y
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at h
    simp only [zoomMetric, one_mul]
    exact (ENNReal.ofReal_eq_ofReal_iff (hDω _ _).1
      (mul_nonneg (Real.exp_pos _).le ENNReal.toReal_nonneg)).mp h

/-- **`ZoomMetricNormAlpha0Stmt` at every universe.** -/
theorem zoomMetricNormAlpha0_stmt_univ : ZoomMetricNormAlpha0Stmt.{u} := by
  intro γ ξ α₀ Ω _ P hC hcirc D hG hD
  exact zoomMetricNormAlpha_of_isLQGMetricOfField_univ hG hD

end HarmonicBalls.FirstPassS11iZoomMetricAlpha0

namespace HarmonicBalls.FirstPassS11iInsertionTransfer

open HarmonicBalls FirstPassS11i

/-- An insertion-`α₀` LQG measure of the field under `P'` is one under every `P ≪ P'` (any universe). -/
theorem isLQGMeasureOfField_of_ae_le_univ {Ω : Type u} [MeasurableSpace Ω] {P P' : Measure Ω} {γ α₀ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (h : P ≪ P') (hμ : IsLQGMeasureOfField P' γ α₀ hcirc μ) :
    IsLQGMeasureOfField P γ α₀ hcirc μ := by
  unfold IsLQGMeasureOfField IsLQGMeasure at *
  exact h.ae_le hμ

/-- **Insertion transfer on a disc avoiding the origin, any universe.** The statement of
`disc_transfer_k0_of_normalizedMetric` for probability spaces in `Type u`. -/
theorem disc_transfer_k0_of_normalizedMetric_univ {γ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCC : CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hCM : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (hB1 : LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{u})
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hzero : AllModelsAt.{u} γ (lqgXi γ) 0 q U V W T Q' Q δ M 0)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hcr : 2 * r < ‖c‖) (hsub : closedBall c (2 * r) ⊆ ball (0 : ℂ) 1)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ (lqgXi γ) α hC D) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball c r →
      WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q := by
  classical
  have hPprob : IsProbabilityMeasure P := isProbabilityMeasure_of_isWholePlaneGFF hGFF
  have hr2 : (0 : ℝ) < 2 * r := by linarith
  have hcl : closedBall c r ⊆ ball c (2 * r) := closedBall_subset_ball (by linarith)
  have hnot : (0 : ℂ) ∉ closedBall c (2 * r) := fun h => by
    have h' := mem_closedBall.1 h
    rw [dist_comm, dist_zero_right] at h'
    linarith
  have hnot0 : (0 : ℂ) ∉ ball c (2 * r) := fun h => hnot (ball_subset_closedBall h)
  -- smooth cut-off of `-α log‖·‖` on the decoder disc, and the Cameron–Martin change of law
  obtain ⟨f, hf, hfc, hf0, hfα⟩ := exists_log_cutoff_avoid_zero α hr2 hcr
  have hfcont : Continuous f := hf.continuous
  obtain ⟨P', hP'P, hPP', hGFF'⟩ := hCM Ω P hC hcirc hGFF f hf hfc hf0
  have hP'prob : IsProbabilityMeasure P' := isProbabilityMeasure_of_isWholePlaneGFF hGFF'
  have hQ : (0 : ℝ) < lqgQ γ := lqgQ_pos_of_pos hγ0
  -- zero-insertion measures of `h` (under `P`) and of `h + f` (under `P'`)
  obtain ⟨μ0, hμ0⟩ := hEx Ω P hC hcirc hGFF hγ0 hγ2 hQ
  obtain ⟨μ', hμ'⟩ := hEx Ω P' (fun ω => addFunPairing (hC ω) f)
    (fun ω r z => hcirc ω r z + Real.circleAverage f z r) hGFF' hγ0 hγ2 hQ
  have hμ'P : IsLQGMeasureOfField P γ 0 (fun ω r z => hcirc ω r z + Real.circleAverage f z r) μ' :=
    isLQGMeasureOfField_of_ae_le_univ hPP' hμ'
  -- the two measures agree on the decoder disc
  have hmeas : ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → s ⊆ ball c (2 * r) → μ' ω s = μ ω s :=
    zeroInsertion_shift_eq_insertion_on_disc hfcont hfα hnot0 hGFF hγ0 hγ2 hα hμ hμ0 hμ'P
  -- the metric of `h + f`: same `𝔇` as the insertion-`α` metric
  obtain ⟨𝔇, h𝔇, hDeq⟩ : ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ (lqgXi γ) 𝔇 ∧
      ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧ ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -α * Real.log ‖x‖) u v := hD
  have hSat0 := h𝔇.satisfiesLQGMetricAxioms_univ Ω P hC hcirc (fun _ _ => (0 : ℝ)) hGFF
    (fun _ => continuous_const) (fun _ => measurable_const)
  have hbase : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) u v) =
      weylScaling (𝔇 (hC ω)) (lqgXi γ) f u v := by
    filter_upwards [hSat0.ae_weylScaling] with ω hω u v
    have h := hω f hfcont u v
    simpa only [addFunPairing_zero_fun] using h
  have hLen0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [hSat0.ae_isEuclideanLengthMetric] with ω hω
    simpa only [addFunPairing_zero_fun] using hω
  have hSat' := h𝔇.satisfiesLQGMetricAxioms_univ Ω P hC hcirc (fun _ => f) hGFF
    (fun _ => hfcont) (fun _ => measurable_const)
  have hLen' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (addFunPairing (hC ω) f)) :=
    hSat'.ae_isEuclideanLengthMetric
  have hDnn' : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ 𝔇 (addFunPairing (hC ω) f) u v :=
    hLen'.mono fun ω hω u v => nonneg_of_isEuclideanLengthMetric hω u v
  have hD'P : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ 𝔇 (addFunPairing (hC ω) f) u v ∧
      ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) u v) =
        weylScaling (𝔇 (addFunPairing (hC ω) f)) (lqgXi γ) (fun x => -(0 : ℝ) * Real.log ‖x‖) u v := by
    filter_upwards [hSat'.ae_weylScaling, hDnn'] with ω hω hnn u v
    refine ⟨hnn u v, ?_⟩
    have h := hω (fun _ => (0 : ℝ)) continuous_const u v
    simp only [addFunPairing_zero_fun, neg_zero, zero_mul] at h ⊢
    exact h
  have hD'mod : IsLQGMetricOfField P' γ (lqgXi γ) 0 (fun ω => addFunPairing (hC ω) f)
      (fun ω => 𝔇 (addFunPairing (hC ω) f)) :=
    ⟨𝔇, h𝔇, hP'P.ae_le hD'P⟩
  -- the zero-insertion statement, applied under the Cameron–Martin law
  have hz := hzero Ω P' (fun ω => addFunPairing (hC ω) f)
    (fun ω r z => hcirc ω r z + Real.circleAverage f z r) μ' (fun ω => 𝔇 (addFunPairing (hC ω) f))
    hGFF' hμ' hD'mod
  unfold PhysicalAt at hz
  simp only [pow_zero, one_mul] at hz
  have hzP := hPP'.ae_le hz
  -- decoders of the disc (`κ` for the measure, `m` for the metric)
  obtain ⟨κ, -, hκcal, -⟩ := hK c c r (2 * r) hγ0 hγ2 hr hr2 hcl hsub hnot
  obtain ⟨m, -, hm18⟩ := localMetricReplacement_unrooted_derived (ξ := lqgXi γ) hB1
    DerivedInputs9.cameronMartinGFFMutualAbsCont_derived
    (lqgInternalMetricWeylAeMeasurable_of_fieldAxioms_of_truncation hLF weylLogTruncationStatement_holds)
    (fun α' _ Ω' _ P' _ hC' hcirc' => hLF Ω' P' γ (lqgXi γ) α' hC' hcirc')
    hγ0 hγ2 hr2 hnot h𝔇
  obtain ⟨mm, hmm0, hmmm⟩ : ∃ mm : DecObs (ball c (2 * r)) → ℂ → ℂ → ℝ,
      (∀ obs x y, 0 ≤ mm obs x y) ∧ ∀ (obs : DecObs (ball c (2 * r))) (x y : ℂ)
        (h : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r)),
        ENNReal.ofReal (mm obs x y) = ENNReal.ofReal (m obs ⟨(x, y), h⟩) := by
    refine ⟨fun obs x y => if h : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r) then
      max (m obs ⟨(x, y), h⟩) 0 else 0, fun obs x y => ?_, fun obs x y h => ?_⟩
    · by_cases h : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r)
      · simp only [h, ↓reduceDIte]
        exact le_max_right _ _
      · simp only [h, ↓reduceDIte, le_refl]
    · simp only [h, ↓reduceDIte]
      rcases le_total (m obs ⟨(x, y), h⟩ : ℝ) 0 with h' | h'
      · rw [max_eq_right h', ENNReal.ofReal_of_nonpos h', ENNReal.ofReal_zero]
      · rw [max_eq_left h']
  -- calibration of `κ` and `mm` on the insertion-`α` model
  have hκα : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (localMeanZeroObs α (ball c (2 * r)) (hC ω))).restrict (ball c (2 * r)) =
        ENNReal.ofReal a • (μ ω).restrict (ball c (2 * r)) :=
    hκcal α hα Ω P hC hcirc μ hGFF hμ
  have hint : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ ball c (2 * r), ∀ y ∈ ball c (2 * r),
      ENNReal.ofReal (mm (localMeanZeroObs α (ball c (2 * r)) (hC ω)) x y) =
        ENNReal.ofReal b * internalMetric (D ω) (ball c (2 * r)) x y := by
    filter_upwards [hm18 α hα Ω P hC hcirc hGFF, hDeq] with ω hω hDω
    obtain ⟨b, hb, hbm⟩ := hω
    refine ⟨b, hb, fun x hx y hy => ?_⟩
    have hxy : (x, y) ∈ ball c (2 * r) ×ˢ ball c (2 * r) := ⟨hx, hy⟩
    rw [hmmm _ x y hxy]
    have hfun : D ω = fun u v =>
        (weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun z => -α * Real.log ‖z‖) u v).toReal := by
      funext u v
      rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
    rw [hfun]
    exact hbm ⟨(x, y), hxy⟩
  have hDnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y := hDeq.mono fun ω h x y => (h x y).1
  have hLenα : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    HarmonicBalls.FirstPassS11iStep8LengthMetric.ae_isEuclideanLengthMetric_of_fieldAxioms
      (hLF Ω P γ (lqgXi γ) α hC hcirc) hGFF hγ0 hγ2 hα h𝔇 hDeq
  have hfitα := HarmonicBalls.FirstPassS11iStep8Fitting.ae_fitting_eventually_of_decoders α δ M
    (pinchOmegaGeom W Q δ) U V W T Q' Q c (2 * r) hC μ D κ mm hCC hU hκα
    (ae_of_all P fun ω x y => hmm0 _ x y) hDnn hLenα hint
  -- the zero-insertion side: same decoders, identical observations and internal metrics
  have hobs : ∀ ω, (fun φ : {φ : ℂ → ℝ // IsTestFunction (ball c (2 * r)) φ ∧ ∫ x, φ x = 0} =>
      fieldPairing 0 (addFunPairing (hC ω) f) φ.1) =
        localMeanZeroObs α (ball c (2 * r)) (hC ω) := by
    intro ω
    funext φ
    exact fieldPairing_shift_eq_on_disc φ.1 φ.2.1.2.2 hfα
  have hκ0 : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (fun φ => fieldPairing 0 (addFunPairing (hC ω) f) φ.1)).restrict (ball c (2 * r)) =
        ENNReal.ofReal a • (μ' ω).restrict (ball c (2 * r)) := by
    filter_upwards [hκα, hmeas] with ω hκω hmω
    obtain ⟨a, ha, hωa⟩ := hκω
    refine ⟨a, ha, ?_⟩
    have hres : (μ' ω).restrict (ball c (2 * r)) = (μ ω).restrict (ball c (2 * r)) :=
      restrict_eq_of_subset_eq measurableSet_ball hmω
    rw [hobs ω, hres]
    exact hωa
  have hD'eq : ∀ᵐ ω ∂P, internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c (2 * r)) =
      internalMetric (D ω) (ball c (2 * r)) := by
    filter_upwards [hbase, hDeq, hLen0, hDnn'] with ω hbω hDω hLω hnn
    have hF : 𝔇 (addFunPairing (hC ω) f) = fun u v =>
        (weylScaling (𝔇 (hC ω)) (lqgXi γ) f u v).toReal := by
      funext u v
      rw [← hbω u v, ENNReal.toReal_ofReal (hnn u v)]
    have hG : D ω = fun u v =>
        (weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun z => -α * Real.log ‖z‖) u v).toReal := by
      funext u v
      rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
    rw [hF, hG]
    funext x y
    exact (internalMetric_shift_eq_on_disc (ξ := lqgXi γ) (α := α) hLω hfcont hfc hr2 hfα).symm
  have hint0 : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ ball c (2 * r), ∀ y ∈ ball c (2 * r),
      ENNReal.ofReal (mm (fun φ => fieldPairing 0 (addFunPairing (hC ω) f) φ.1) x y) =
        ENNReal.ofReal b * internalMetric (𝔇 (addFunPairing (hC ω) f)) (ball c (2 * r)) x y := by
    filter_upwards [hint, hD'eq] with ω hω heq
    obtain ⟨b, hb, hbx⟩ := hω
    refine ⟨b, hb, fun x hx y hy => ?_⟩
    rw [hobs ω, heq]
    exact hbx x hx y hy
  have hfit0 := HarmonicBalls.FirstPassS11iStep8Fitting.ae_fitting_eventually_of_decoders 0 δ M
    (pinchOmegaGeom W Q δ) U V W T Q' Q c (2 * r) (fun ω => addFunPairing (hC ω) f) μ'
    (fun ω => 𝔇 (addFunPairing (hC ω) f)) κ mm hCC hU hκ0 (ae_of_all P fun ω x y => hmm0 _ x y)
    hDnn' hLen' hint0
  -- the eventual certificate identity at every centre of the decoder disc
  have hiff : ∀ᵐ ω ∂P, ∀ z ∈ ball c (2 * r), ∀ᶠ n : ℕ in atTop,
      (CertificateEvent (μ' ω) (𝔇 (addFunPairing (hC ω) f)) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ)⁻¹ ^ n) z ↔
        CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) z) := by
    filter_upwards [hfit0, hfitα] with ω h0 h1 z hz
    filter_upwards [h0 z hz, h1 z hz] with n e0 e1
    have e0' : CertificateEvent (κ (localMeanZeroObs α (ball c (2 * r)) (hC ω)))
        (mm (localMeanZeroObs α (ball c (2 * r)) (hC ω))) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z ↔
        CertificateEvent (μ' ω) (𝔇 (addFunPairing (hC ω) f)) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          ((2 : ℝ)⁻¹ ^ n) z := by
      rw [← hobs ω]
      exact e0
    exact e0'.symm.trans e1
  -- transfer the window limit from `μ'` to `μ` on the decoder disc, then to the root ball
  filter_upwards [hzP, hiff, hmeas] with ω hzω hiffω hmω
  have hres : (μ' ω).restrict (ball c (2 * r)) = (μ ω).restrict (ball c (2 * r)) :=
    restrict_eq_of_subset_eq measurableSet_ball hmω
  have hA := ae_restrict_of_ae (s := ball c (2 * r)) hzω
  rw [hres] at hA
  have hB : ∀ᵐ z ∂(μ ω), z ∈ ball c (2 * r) → (z ∈ ball (0 : ℂ) 1 →
      WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q) := by
    refine (ae_restrict_iff' measurableSet_ball).1 ?_
    filter_upwards [hA, ae_restrict_mem measurableSet_ball] with z hz hzs
    intro hz1
    exact (tendsto_window_iff_of_eventually_iff (hiffω z hzs) q).mp (hz hz1)
  filter_upwards [hB] with z hz hzr
  have hzd : z ∈ ball c (2 * r) := ball_subset_ball (by linarith) hzr
  exact hz hzd (hsub (ball_subset_closedBall hzd))

/-- **Insertion transfer at unit scale, any universe.** The scale-`0` insertion-zero statement over `Type u` implies
the scale-`0` insertion-`α` statement over `Type u`. -/
theorem allModelsAt_insertion_of_zero_k0_of_normalizedMetric_univ {γ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCM : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    (hEx : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNon : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (hB1 : LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{u})
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hzero : AllModelsAt.{u} γ (lqgXi γ) 0 q U V W T Q' Q δ M 0) :
    AllModelsAt.{u} γ (lqgXi γ) α q U V W T Q' Q δ M 0 := by
  intro Ω _ P hC hcirc μ D hGFF hμ hD
  classical
  have hPprob : IsProbabilityMeasure P := isProbabilityMeasure_of_isWholePlaneGFF hGFF
  have hU : U ⊆ closedBall 0 7 := by
    intro z hz
    have h2 : dist z 0 < 2 := (hgeom.U_subset hz).1
    exact mem_closedBall.2 (by linarith)
  have hCC := FirstPassS11ap.certificateContainments_of_buffered hgeom
  have hNonω : ∀ᵐ ω ∂P, μ ω {0} = 0 :=
    (hNon Ω P hC hcirc hGFF hγ0 hγ2 hα μ hμ).mono fun ω h => h 0
  have hΦ : ∀ p : ℚ × ℚ × ℚ, HarmonicBalls.FirstPassS11iStep8Exhaustion.ValidBall p → ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (HarmonicBalls.FirstPassS11iStep8Exhaustion.ballCen p) (HarmonicBalls.FirstPassS11iStep8Exhaustion.ballRad p) →
      WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q := fun p hp =>
    disc_transfer_k0_of_normalizedMetric_univ hγ0 hγ2 hα hCC hU hCM hEx hK hB1 hLF hzero hp.1 hp.2.1 (validBall_closedBall_sub hp)
      Ω P hC hcirc μ D hGFF hμ hD
  have hcov := HarmonicBalls.FirstPassS11iStep8Exhaustion.ae_forall_of_cover P μ
    (fun ω z => WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q) hNonω hΦ
  unfold PhysicalAt
  simp only [pow_zero, one_mul]
  exact hcov

end HarmonicBalls.FirstPassS11iInsertionTransfer

namespace HarmonicBalls.FirstPassS11iStep8PhysExists

open FirstPassS11i HarmonicBalls
open HarmonicBalls.FirstPassS11iHzoom HarmonicBalls.FirstPassS11iStep8Zoom

/-- At the scale `k = 0` the physical statement is the unit-ball frequency (any universe). -/
theorem physicalAt_zero_of_unitBall_univ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {q δ M : ℝ}
    {U V W T Q' Q : Set ℂ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : UnitBallFrequencyStmt P q U V W T Q' Q δ M μ D) :
    PhysicalAt P q U V W T Q' Q δ M 0 μ D := by
  unfold UnitBallFrequencyStmt at h
  unfold PhysicalAt
  simpa only [pow_zero, one_mul] using h

/-- The insertion-zero unit frequency gives the insertion-zero statement at scale `0` (any universe). -/
theorem allModelsAt_zero_scale_zero_of_unit_univ {γ q δ M : ℝ} {U V W T Q' Q : Set ℂ} {F : Set Step8Code}
    (hU : InsertionZeroUnitStmt.{u} γ F U V W T Q' Q δ M) (hq : CommonProb.{u} γ F q) :
    AllModelsAt.{u} γ (lqgXi γ) 0 q U V W T Q' Q δ M 0 := by
  intro Ω _ P hC hcirc μ D hG hμ hD
  exact physicalAt_zero_of_unitBall_univ (hU Ω P hC hcirc μ D hG hμ hD q hq)

/-- **Route 1 zoom (insertion `α`), any universe.** -/
theorem hzoom_alpha_all_of_scale_zero_univ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α q δ M : ℝ}
    {U V W T Q' Q : Set ℂ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {D : Ω → ℂ → ℂ → ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : IsLQGMetricOfField P γ ξ α hC D) (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (h0 : AllModelsAt.{u} γ ξ α q U V W T Q' Q δ M 0) :
    ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      ∀ᵐ w ∂(ENNReal.ofReal a • zoomMeasure (μ ω) k), w ∈ ball (0 : ℂ) 1 →
        Tendsto (fun N : ℕ => (({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
          CertificateEvent (ENNReal.ofReal a • zoomMeasure (μ ω) k) (fun x y => b * zoomMetric (D ω) k x y)
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M ((2 : ℝ)⁻¹ ^ n) w}.ncard : ℕ) : ℝ) / (N : ℝ))
          atTop (𝓝 q) := by
  intro k
  obtain ⟨Dk, hDk, hscale⟩ :=
    HarmonicBalls.FirstPassS11iZoomMetricAlpha0.zoomMetricNormAlpha_of_isLQGMetricOfField_univ hG hD k
  have hR : (2 : ℝ) ^ k ≠ 0 := by positivity
  have hGk := isWholePlaneGFF_normalized hG hR
  have hμk := HarmonicBalls.FirstPassS11iStep8PhysReduction.isLQGMeasureOfField_normMeasureAlpha
    hγ0 hγ2 hα hG hμ hCC k
  have hU := h0 Ω P (normField ((2 : ℝ) ^ k) hC hcirc) (normCirc ((2 : ℝ) ^ k) hcirc)
    (HarmonicBalls.FirstPassS11iStep8PhysReduction.normMeasureAlpha γ α μ hcirc k) Dk hGk hμk hDk
  unfold PhysicalAt at hU
  filter_upwards [hU, hscale] with ω hω hsc
  obtain ⟨B, hB, hBeq⟩ := hsc
  have hmet : (fun x y => B⁻¹ * zoomMetric (D ω) k x y) = Dk ω := by
    funext x y
    rw [hBeq x y, ← mul_assoc, inv_mul_cancel₀ hB.ne', one_mul]
  refine ⟨Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 + (lqgQ γ - α) * Real.log ((2 : ℝ) ^ k)))), B⁻¹,
    Real.exp_pos _, inv_pos.mpr hB, ?_⟩
  have hmeas : ENNReal.ofReal (Real.exp (γ * (-(hcirc ω ((2 : ℝ) ^ k) 0 +
      (lqgQ γ - α) * Real.log ((2 : ℝ) ^ k))))) • zoomMeasure (μ ω) k =
      HarmonicBalls.FirstPassS11iStep8PhysReduction.normMeasureAlpha γ α μ hcirc k ω := rfl
  rw [hmeas, hmet]
  simp only [pow_zero, one_mul] at hω
  exact hω

/-- **Route 1: every scale at insertion `α`, any universe.** -/
theorem allModelsAt_all_scales_of_scale_zero_univ {γ ξ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCCα : HarmonicBalls.FirstPassS11iStep8PhysReduction.CoordChangeAlpha0Stmt.{u})
    (h0 : AllModelsAt.{u} γ ξ α q U V W T Q' Q δ M 0) (k : ℕ) :
    AllModelsAt.{u} γ ξ α q U V W T Q' Q δ M k := by
  intro Ω _ P hC hcirc μ D hG hμ hD
  unfold PhysicalAt
  exact (HarmonicBalls.FirstPassS11iStep8Transfer.hphys_of_zoom_const_family P U V W T Q' Q δ M q μ D
    (hzoom_alpha_all_of_scale_zero_univ hγ0 hγ2 hα hG hμ hD (hCCα γ α Ω P hC hcirc) h0)) k

/-- **`Step8PhysExistsStmt` at every universe from the event calibration and the metric field axioms.** Route 1: the
calibration gives the pinch event and the insertion-zero unit frequency; the unit-scale insertion transfer
(`allModelsAt_insertion_of_zero_k0_of_normalizedMetric_univ`, whose other inputs are theorems) gives the insertion-`α`
statement at scale `0`; the zoom gives every scale. -/
theorem step8PhysExists_of_calibration_fieldAxioms_univ (hCal : Step8EventCalibrationStmt.{u})
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{u}) : Step8PhysExistsStmt.{u} := by
  intro U V W T Q' Q δ hgeom γ α M hγ0 hγ2 hα hM hE
  obtain ⟨E, F, hPG, hcal, hU⟩ := hCal U V W T Q' Q δ M γ hgeom hγ0 hγ2 hM hE
  refine ⟨E, hPG, fun q hq k => ?_⟩
  exact allModelsAt_all_scales_of_scale_zero_univ hγ0 hγ2 hα coordChangeAlpha0Stmt_holds.{u}
    (FirstPassS11iInsertionTransfer.allModelsAt_insertion_of_zero_k0_of_normalizedMetric_univ hgeom hγ0 hγ2 hα
      S11aj.cameronMartinGFFReweighting_derived
      (fun Ω _ P hC hcirc => lqgMeasureExistence_forall_zero γ Ω P hC hcirc)
      (fun Ω _ P hC hcirc => lqgMeasureNonatomic_holds Ω P γ α hC hcirc)
      (fun c₁ c₂ r₁ r₂ => LocalDecoderCommon.localMeasureKernelStmt_derived γ c₁ c₂ r₁ r₂)
      localLQGMetricNormalizedMeasurableFixedMetric_derived hLF
      (allModelsAt_zero_scale_zero_of_unit_univ hU (hcal q hq))) k

/-- **The Step 8 identity at every universe from the event calibration and the metric field axioms.** -/
theorem step8Identity_given_pinchEvent_canonical_of_calibration_fieldAxioms_univ
    (hCal : Step8EventCalibrationStmt.{u}) (hLF : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    Step8IdentityGivenPinchEventCanonicalStmt.{u} :=
  step8Identity_given_pinchEvent_canonical_of_physExists (step8PhysExists_of_calibration_fieldAxioms_univ hCal hLF)

end HarmonicBalls.FirstPassS11iStep8PhysExists
