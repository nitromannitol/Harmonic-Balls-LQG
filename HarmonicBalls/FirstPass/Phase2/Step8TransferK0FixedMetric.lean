import HarmonicBalls.FirstPass.Phase2.Step8TransferK0Unrooted
import HarmonicBalls.FirstPass.Phase2.Step8InsertionZeroUnitFixedMetric

/-!
# Step 8 of Lemma 11.13: insertion transfer at unit scale for one fixed LQG metric

`allModelsAt_insertion_of_zero_k0_of_normalizedMetric` (`Phase2/Step8TransferK0Unrooted.lean`) transfers the unit-scale
certificate frequency from all insertion-zero LQG models to all insertion-`α` models. Its proof uses the zero-insertion
hypothesis only at the Cameron-Martin shifted model `h + f`, whose metric is `𝔇 (h + f)` for the same LQG metric `𝔇`
as the insertion-`α` model. So the transfer holds for the models of one fixed LQG metric:

* `disc_transfer_k0_fixedMetric`, `allModelsAt_insertion_of_zero_k0_fixedMetric`: the two theorems of that file, with
  the models restricted to those whose metric is, almost surely, the Weyl scaling of one fixed `𝔇` at their field;
* `physicalAt_zero_of_unitBallFrequency`: the unit-ball frequency is the physical frequency at scale `2⁰`;
* `physicalAt_insertion_fixedMetric_of_seed`: for a coding event `E` satisfying the seed of Lemma 11.12 for `𝔇` and
  a common probability `q` of `E`, every insertion-`α` model of `𝔇` (`α < Q_γ`) has the unit-scale certificate
  frequency `q`. Remaining inputs: the local metric replacement `hR`, `hfr` and the field axioms `hAx`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.FirstPassS11iInsertionTransfer

open HarmonicBalls FirstPassS11i

/-- **Insertion transfer on a disc avoiding the origin, for one fixed LQG metric.** Let `𝔇` be an LQG metric. If
every whole-plane insertion-zero model whose metric is, almost surely, the Weyl scaling of `𝔇` at its field has the
unit-scale certificate frequency `q` (`hzero`), then so has, on a disc `B(c, r)` with `2r < |c|`, every insertion-`α`
model whose metric is, almost surely, the Weyl scaling of `𝔇` at its field with the `α`-log singularity. Proof of
`disc_transfer_k0_of_normalizedMetric`: the Cameron-Martin shifted model keeps the metric `𝔇`. -/
theorem disc_transfer_k0_fixedMetric {γ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCC : CertificateContainments δ (pinchOmegaGeom W Q δ) V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (hCM : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{0})
    (hEx : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hB1 : LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{0})
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{0})
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇)
    (hzero : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -0 * Real.log ‖x‖) u v) →
        PhysicalAt P q U V W T Q' Q δ M 0 μ D)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (hcr : 2 * r < ‖c‖) (hsub : closedBall c (2 * r) ⊆ ball (0 : ℂ) 1)
    (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -α * Real.log ‖x‖) u v) :
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
    isLQGMeasureOfField_of_ae_le hPP' hμ'
  -- the two measures agree on the decoder disc
  have hmeas : ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → s ⊆ ball c (2 * r) → μ' ω s = μ ω s :=
    zeroInsertion_shift_eq_insertion_on_disc hfcont hfα hnot0 hGFF hγ0 hγ2 hα hμ hμ0 hμ'P
  -- the metric of `h + f`: same `𝔇` as the insertion-`α` metric
  have hDeq := hD
  have hSat0 := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => (0 : ℝ)) hGFF
    (fun _ => continuous_const) (fun _ => measurable_const)
  have hbase : ∀ᵐ ω ∂P, ∀ u v, ENNReal.ofReal (𝔇 (addFunPairing (hC ω) f) u v) =
      weylScaling (𝔇 (hC ω)) (lqgXi γ) f u v := by
    filter_upwards [hSat0.ae_weylScaling] with ω hω u v
    have h := hω f hfcont u v
    simpa only [addFunPairing_zero_fun] using h
  have hLen0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [hSat0.ae_isEuclideanLengthMetric] with ω hω
    simpa only [addFunPairing_zero_fun] using hω
  have hSat' := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ => f) hGFF
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
  have hD'mod := hP'P.ae_le hD'P
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

/-- **Insertion transfer at unit scale for one fixed LQG metric.** The statement of
`allModelsAt_insertion_of_zero_k0_of_normalizedMetric` with the models restricted to those whose metric is, almost
surely, the Weyl scaling of one fixed LQG metric `𝔇` at their field (insertion `0` in the hypothesis, insertion `α` in
the conclusion). -/
theorem allModelsAt_insertion_of_zero_k0_fixedMetric {γ α q δ M : ℝ} {U V W T Q' Q : Set ℂ}
    (hgeom : IsBufferedPinchGeometry U V W T Q' Q δ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hCM : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{0})
    (hEx : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hNon : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α hC hcirc)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hB1 : LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{0})
    (hLF : LQGMetricFieldAxiomsUnivFrozen.{0})
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ (lqgXi γ) 𝔇)
    (hzero : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -0 * Real.log ‖x‖) u v) →
        PhysicalAt P q U V W T Q' Q δ M 0 μ D) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -α * Real.log ‖x‖) u v) →
        PhysicalAt P q U V W T Q' Q δ M 0 μ D := by
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
    disc_transfer_k0_fixedMetric hγ0 hγ2 hα hCC hU hCM hEx hK hB1 hLF h𝔇 hzero hp.1 hp.2.1 (validBall_closedBall_sub hp)
      Ω P hC hcirc μ D hGFF hμ hD
  have hcov := HarmonicBalls.FirstPassS11iStep8Exhaustion.ae_forall_of_cover P μ
    (fun ω z => WinLim (fun n : ℕ => CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
        ((2 : ℝ)⁻¹ ^ n) z) q) hNonω hΦ
  unfold PhysicalAt
  simp only [pow_zero, one_mul]
  exact hcov

/-- The unit-ball frequency statement of a model is its physical frequency statement at scale `2⁰`. -/
theorem physicalAt_zero_of_unitBallFrequency {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {q δ M : ℝ}
    {U V W T Q' Q : Set ℂ} {μ : Ω → Measure ℂ} {D : Ω → ℂ → ℂ → ℝ}
    (h : HarmonicBalls.FirstPassS11iHzoom.UnitBallFrequencyStmt P q U V W T Q' Q δ M μ D) :
    PhysicalAt P q U V W T Q' Q δ M 0 μ D := by
  unfold PhysicalAt
  simp only [pow_zero, one_mul]
  exact h

end HarmonicBalls.FirstPassS11iInsertionTransfer

open ProbabilityTheory
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
  HarmonicBalls.FirstPassS11iHzoomUnitBallFit HarmonicBalls.FirstPassS11iHzoom

namespace HarmonicBalls.FirstPassPhase2Step8TransferK0FixedMetric

open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai FirstPassS11ah
open HarmonicBalls.FirstPassS11iStep8PhysExists HarmonicBalls.FirstPassS11iHzoomUnitBallDoubled
open HarmonicBalls.FirstPassPhase2Step8InsertionZeroUnitFixedMetric

/-- **Unit-scale certificate frequency of every insertion-`α` model of one fixed LQG metric, from the seed of
Lemma 11.12.** Let `𝔇` be an LQG metric and `E` a measurable coding event satisfying the seed `hEq` for `𝔇`, and let
`q` be a common probability of `E`. Then for `α < Q_γ`, every whole-plane insertion-`α` model whose metric is, almost
surely, the Weyl scaling of `𝔇` at its field with the `α`-log singularity has the certificate frequency `q` at scale
`2⁰`. The Cameron-Martin reweighting, the existence and non-atomicity of the LQG measure, the local measure kernel and
the normalized decoder of a fixed LQG metric are supplied by their proofs; the remaining inputs are `hR`, `hfr` and
`hAx`. -/
theorem physicalAt_insertion_fixedMetric_of_seed {γ α δ M : ℝ} {U V W T Q' Q : Set ℂ} {E : Set Step8Code}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ (lqgXi γ) c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hAx : LQGMetricFieldAxiomsUnivFrozen.{0})
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : HarmonicBalls.IsLQGMetric γ (lqgXi γ) 𝔇) (hE : MeasurableSet E)
    (hEq : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ γ hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -γ * Real.log ‖x‖) u v) →
        ∀ᵐ ω ∂P, (localModConstField γ hC (ball (0 : ℂ) 7) ω ∈ E ↔
          FirstPassS11i.CertificateEvent (μ ω) (D ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0))
    {q : ℝ} (hq : CommonProb.{0} γ E q) :
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
        ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) (lqgXi γ) (fun x => -α * Real.log ‖x‖) u v) →
        HarmonicBalls.FirstPassS11iInsertionTransfer.PhysicalAt P q U V W T Q' Q δ M 0 μ D :=
  FirstPassS11iInsertionTransfer.allModelsAt_insertion_of_zero_k0_fixedMetric hgeo hγ0 hγ2 hα
    S11aj.cameronMartinGFFReweighting_derived
    (fun Ω _ P hC hcirc => lqgMeasureExistence_forall_zero γ Ω P hC hcirc)
    (fun Ω _ P hC hcirc => lqgMeasureNonatomic_holds Ω P γ α hC hcirc)
    (fun c₁ c₂ r₁ r₂ => LocalDecoderCommon.localMeasureKernelStmt_derived γ c₁ c₂ r₁ r₂)
    localLQGMetricNormalizedMeasurableFixedMetric_derived.{0} hAx h𝔇
    (fun Ω _ P hC hcirc μ D hG hμ hD =>
      FirstPassS11iInsertionTransfer.physicalAt_zero_of_unitBallFrequency
        (insertionZeroUnit_of_seed_fixedMetric hγ0 hγ2 hgeo hR hfr hAx h𝔇 hE hEq Ω P hC hcirc μ D hG hμ hD q hq))

end HarmonicBalls.FirstPassPhase2Step8TransferK0FixedMetric
