import HarmonicBalls.FirstPass.Phase2.CanonicalLift
import HarmonicBalls.FirstPass.Phase2.InternalMetricWeylAeMeasurableDerived
import HarmonicBalls.FirstPass.Phase2.WeylLogTruncationDerivedInputs
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsDerived
import HarmonicBalls.Steps.Sec11.ContinuousFieldShift
import HarmonicBalls.Proofs.GFF.DistributionMetricDecoder
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling

/-!
# The singular LQG metric as a measurable functional of the canonical field

Fix a γ-LQG metric `𝔇₀` with Weyl exponent `ξ = γ / d_γ` (`LQGMetric.xiGamma γ`). For a point `L` of the canonical
space (pairings with mean-zero test functions, i.e. a field modulo additive constants), the decoder
`canonSingularLimsup 𝔇₀ α₀ L u v` is the limsup over `k` of the metrics `𝔇₀` of the log-cutoff fields
`canonLift α₀ L - α₀ log max(|·|, e^{-k})`. It is measurable in `L` (`measurable_canonSingularLimsup`).

Main result (`ae_eq_mul_canonSingularLimsup`): for `γ ∈ (0, 2)` and `α₀ < Q`, if `D` is the LQG metric of
`h = h^ℂ - α₀ log |·|` (`IsLQGMetricOfField`, with any γ-LQG metric `𝔇`), there is a deterministic `C > 0` such that
for every pair of points, almost surely
`D(u, v) = C e^{ξ (h^ℂ, unitTest)} · canonSingularLimsup 𝔇₀ α₀ (alphaCanon α₀ hC ω) u v`.
The random factor `e^{ξ (h^ℂ, unitTest)}` is the Weyl scaling by the additive constant that the canonical field
forgets. Inputs, all proved: the uniqueness of the γ-LQG metric (Gwynne-Miller 2021, Theorem 1.2,
`exists_pos_ae_eq_const_mul_of_isLQGMetric`) at each cutoff field, the truncation limit of the singular Weyl
scaling (`ae_tendsto_singularCutoff_of_truncation`), Weyl scaling by a random constant
(`IsWholePlaneGFF.ae_metric_background_add_random_constant`), and the lift of the canonical field
(`IsWholePlaneGFF.ae_comp_canonLift_alphaCanon`).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology
open HarmonicBalls.DecoderInputsDerived
open scoped ENNReal

/-- The singular metric decoder at a canonical field `L`: the limsup over `k` of the metrics `𝔇₀` of the log-cutoff
fields `canonLift α₀ L - α₀ log max(|·|, e^{-k})`, at the pair of points `(u, v)`. -/
noncomputable def canonSingularLimsup (𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (α₀ : ℝ) (L : S11n.CanonSpace)
    (u v : ℂ) : ℝ≥0∞ :=
  singularCutoffLimsup 𝔇₀ α₀ (canonLift α₀ L) u v

/-- The singular metric decoder is measurable on the canonical space. -/
theorem measurable_canonSingularLimsup {γ ξ : ℝ} {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ ξ 𝔇₀)
    (α₀ : ℝ) (u v : ℂ) : Measurable fun L : S11n.CanonSpace => canonSingularLimsup 𝔇₀ α₀ L u v :=
  (measurable_singularCutoffLimsup h𝔇₀ α₀ u v).comp (measurable_canonLift α₀)

/-- **Cutoff metrics of the lifted canonical field.** Almost surely, for every cutoff level `k`, the metric of the
lifted canonical field with the cutoff `-α₀ log max(|·|, e^{-k})` is `e^{-ξ (h^ℂ, unitTest)}` times the metric of
`h^ℂ - α₀ log max(|·|, e^{-k})`. -/
theorem IsWholePlaneGFF.ae_cutoff_canonLift_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc) {γ ξ : ℝ}
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ ξ 𝔇₀) (α₀ : ℝ) (u v : ℂ) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      𝔇₀ (addFunPairing (canonLift α₀ (alphaCanon α₀ hC ω)) (logCutoffWeight α₀ k)) u v =
        Real.exp (ξ * -hC ω unitTest) * 𝔇₀ (addFunPairing (hC ω) (logCutoffWeight α₀ k)) u v := by
  rw [ae_all_iff]
  intro k
  have hF : Measurable[distributionMeasurableSpace]
      fun T : (ℂ → ℝ) → ℝ => 𝔇₀ (addFunPairing T (logCutoffWeight α₀ k)) u v :=
    (h𝔇₀.measurable_apply u v).comp (measurable_addFunPairing_distribution_self (logCutoffWeight α₀ k))
  have hc : Measurable fun ω => -hC ω unitTest := (h.measurable_pairing _ unitTest_isTestFunction).neg
  filter_upwards [h.ae_comp_canonLift_alphaCanon α₀ _ hF,
    h.ae_metric_background_add_random_constant 𝔇₀ h𝔇₀ (logCutoffWeight α₀ k)
      (continuous_logCutoffWeight α₀ k) _ hc] with ω h1 h2
  have h1' : 𝔇₀ (addFunPairing (canonLift α₀ (alphaCanon α₀ hC ω)) (logCutoffWeight α₀ k)) u v =
      𝔇₀ (addFunPairing (addFunPairing (hC ω) (fun _ => -hC ω unitTest)) (logCutoffWeight α₀ k)) u v := h1
  have h2' : 𝔇₀ (addFunPairing (hC ω) (fun z => logCutoffWeight α₀ k z + -hC ω unitTest)) u v =
      Real.exp (ξ * -hC ω unitTest) * 𝔇₀ (addFunPairing (hC ω) (logCutoffWeight α₀ k)) u v := h2 u v
  rw [h1', h𝔇₀.addFunPairing_addFunPairing (hC ω) continuous_const (continuous_logCutoffWeight α₀ k), ← h2']
  congr 3
  funext z
  exact add_comm _ _

/-- **Identification of the singular LQG metric through the canonical field.** For `γ ∈ (0, 2)`, `α₀ < Q` and a
reference γ-LQG metric `𝔇₀` with Weyl exponent `ξ = γ / d_γ`: if `D` is the LQG metric of `h^ℂ - α₀ log |·|`, then for
some deterministic `C > 0` and every pair of points `(u, v)`, almost surely
`D(u, v) = C e^{ξ (h^ℂ, unitTest)} · canonSingularLimsup 𝔇₀ α₀ (alphaCanon α₀ hC ω) u v`. -/
theorem ae_eq_mul_canonSingularLimsup {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇₀)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ (LQGMetric.xiGamma γ) α₀ hC D) :
    ∃ C : ℝ, 0 < C ∧ ∀ u v : ℂ, ∀ᵐ ω ∂P,
      D ω u v = C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest) *
        (canonSingularLimsup 𝔇₀ α₀ (alphaCanon α₀ hC ω) u v).toReal := by
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  obtain ⟨C, hC0, hU⟩ := exists_pos_ae_eq_const_mul_of_isLQGMetric hγ hγ2 h𝔇₀ h𝔇
    (fun _ hD => LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric hD) ae_eq_comp_of_ae_eq_testPairing
  refine ⟨C, hC0, fun u v => ?_⟩
  have hCne : C ≠ 0 := hC0.ne'
  have hU' : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ a b : ℂ, 𝔇 (addFunPairing (hC ω) (logCutoffWeight α₀ k)) a b =
      C * 𝔇₀ (addFunPairing (hC ω) (logCutoffWeight α₀ k)) a b := by
    rw [ae_all_iff]
    intro k
    exact hU Ω P hC hcirc (fun _ => logCutoffWeight α₀ k) hW (fun _ => continuous_logCutoffWeight α₀ k)
      (fun _ => measurable_const)
  have hTr := ae_tendsto_singularCutoff_of_truncation lqgMetricFieldAxiomsUnivFrozen_derived.{0}
    weylLogTruncationStatement_holds hW hγ hγ2 hα h𝔇 (f := fun _ => 0) continuous_const
  filter_upwards [hDae, hU', hTr, hW.ae_cutoff_canonLift_eq h𝔇₀ α₀ u v] with ω hDω hUω hTω hSω
  have hz : addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := funext fun φ => by simp [addFunPairing]
  have hT := hTω u v
  rw [hz, ← (hDω u v).2] at hT
  have hpos : 0 ≤ Real.exp (LQGMetric.xiGamma γ * -hC ω unitTest) / C := (div_pos (Real.exp_pos _) hC0).le
  have hseq : (fun k : ℕ => ENNReal.ofReal
        (𝔇₀ (addFunPairing (canonLift α₀ (alphaCanon α₀ hC ω)) (logCutoffWeight α₀ k)) u v)) =
      fun k => ENNReal.ofReal (Real.exp (LQGMetric.xiGamma γ * -hC ω unitTest) / C) *
        ENNReal.ofReal (𝔇 (addFunPairing (hC ω) (logCutoffWeight α₀ k)) u v) := by
    funext k
    rw [hSω k, ← ENNReal.ofReal_mul hpos, hUω k u v]
    congr 1
    field_simp
  have hlim : Tendsto (fun k : ℕ => ENNReal.ofReal
        (𝔇₀ (addFunPairing (canonLift α₀ (alphaCanon α₀ hC ω)) (logCutoffWeight α₀ k)) u v)) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (LQGMetric.xiGamma γ * -hC ω unitTest) / C) * ENNReal.ofReal (D ω u v))) := by
    rw [hseq]
    exact ENNReal.Tendsto.const_mul hT (Or.inr ENNReal.ofReal_ne_top)
  have hls : canonSingularLimsup 𝔇₀ α₀ (alphaCanon α₀ hC ω) u v =
      ENNReal.ofReal (Real.exp (LQGMetric.xiGamma γ * -hC ω unitTest) / C) * ENNReal.ofReal (D ω u v) :=
    hlim.limsup_eq
  rw [hls, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpos, ENNReal.toReal_ofReal (hDω u v).1, mul_neg,
    Real.exp_neg]
  have hE : Real.exp (LQGMetric.xiGamma γ * hC ω unitTest) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

/-- Countably many pairs at once: for every sequence of pairs of points, almost surely the identification of
`ae_eq_mul_canonSingularLimsup` holds at all of them, with the same random factor. -/
theorem ae_forall_seq_eq_mul_canonSingularLimsup {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇₀)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ (LQGMetric.xiGamma γ) α₀ hC D) (s : ℕ → ℂ × ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂P, ∀ n : ℕ,
      D ω (s n).1 (s n).2 = C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest) *
        (canonSingularLimsup 𝔇₀ α₀ (alphaCanon α₀ hC ω) (s n).1 (s n).2).toReal := by
  obtain ⟨C, hC0, h⟩ := ae_eq_mul_canonSingularLimsup hγ hγ2 hα h𝔇₀ hW hD
  exact ⟨C, hC0, ae_all_iff.2 fun n => h (s n).1 (s n).2⟩

/-- **The canonical metric decoder.** The continuous metric on `ℂ` with the values of the singular metric decoder
`canonSingularLimsup 𝔇₀ α₀ L` along the dense sequence of `ℂ × ℂ` (`contMetricOfSample`; the Euclidean metric when
these values are not those of a continuous metric). -/
noncomputable def canonMetricDecoder (𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (α₀ : ℝ) (L : S11n.CanonSpace) :
    C(ℂ × ℂ, ℝ) :=
  (contMetricOfSample fun n => (canonSingularLimsup 𝔇₀ α₀ L (TopologicalSpace.denseSeq (ℂ × ℂ) n).1
    (TopologicalSpace.denseSeq (ℂ × ℂ) n).2).toReal).1

/-- The canonical metric decoder is measurable. -/
theorem measurable_canonMetricDecoder {γ ξ : ℝ} {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ ξ 𝔇₀)
    (α₀ : ℝ) : Measurable (canonMetricDecoder 𝔇₀ α₀) :=
  measurable_subtype_coe.comp (measurable_contMetricOfSample.comp
    (measurable_pi_iff.2 fun _ => (measurable_canonSingularLimsup h𝔇₀ α₀ _ _).ennreal_toReal))

/-- **The singular LQG metric is decoded from the canonical field.** For `γ ∈ (0, 2)`, `α₀ < Q` and a reference
γ-LQG metric `𝔇₀` with `ξ = γ / d_γ`: if `D` is the LQG metric of `h^ℂ - α₀ log |·|`, then for some deterministic
`C > 0`, almost surely, for all `u, v`, `D(u, v) = C e^{ξ (h^ℂ, unitTest)} · canonMetricDecoder 𝔇₀ α₀ (alphaCanon α₀ hC ω) (u, v)`.
Route: the identification along the dense sequence (`ae_forall_seq_eq_mul_canonSingularLimsup`); `D` is almost surely
a Euclidean length metric (`ae_weylScaling_singularShift_regular`), hence a continuous metric, so its rescaling is the
continuous metric with these sample values (`contMetricOfSample_contMetricSample`). -/
theorem ae_eq_mul_canonMetricDecoder {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {𝔇₀ : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇₀ : IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇₀)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ (LQGMetric.xiGamma γ) α₀ hC D) :
    ∃ C : ℝ, 0 < C ∧ ∀ᵐ ω ∂P, ∀ u v : ℂ,
      D ω u v = C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest) *
        canonMetricDecoder 𝔇₀ α₀ (alphaCanon α₀ hC ω) (u, v) := by
  obtain ⟨C, hC0, hseq⟩ := ae_forall_seq_eq_mul_canonSingularLimsup hγ hγ2 hα h𝔇₀ hW hD
    (TopologicalSpace.denseSeq (ℂ × ℂ))
  refine ⟨C, hC0, ?_⟩
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  filter_upwards [hseq, hDae, ae_weylScaling_singularShift_regular lqgMetricFieldAxiomsUnivFrozen_derived.{0} hW hγ
    hγ2 hα h𝔇 (f := fun _ => 0) continuous_const] with ω hs hDω hreg
  have hb0 : 0 < C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest) := mul_pos hC0 (Real.exp_pos _)
  set b := C * Real.exp (LQGMetric.xiGamma γ * hC ω unitTest) with hb
  have hz : addFunPairing (hC ω) (fun _ => (0 : ℝ)) = hC ω := funext fun φ => by simp [addFunPairing]
  have hEuc : IsEuclideanLengthMetric (D ω) := by
    have h2 := hreg.2.1
    rw [hz] at h2
    have hfun : D ω = fun u v =>
        (weylScaling (𝔇 (hC ω)) (LQGMetric.xiGamma γ) (fun z => -α₀ * Real.log ‖z‖) u v).toReal := by
      funext u v
      rw [← (hDω u v).2, ENNReal.toReal_ofReal (hDω u v).1]
    rw [hfun]
    exact h2
  obtain ⟨d, hd, -⟩ :=
    LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric ((LPBridge.isEuclideanLengthMetric_iff _).1 hEuc)
  have hdp : ∀ p : ℂ × ℂ, d.1 p = D ω p.1 p.2 := fun p => by
    rw [← hd p.1 p.2]
  have hsample : (fun n => (canonSingularLimsup 𝔇₀ α₀ (alphaCanon α₀ hC ω)
      (TopologicalSpace.denseSeq (ℂ × ℂ) n).1 (TopologicalSpace.denseSeq (ℂ × ℂ) n).2).toReal) =
      contMetricSample (LQGMetric.ContMetric.smul b⁻¹ (inv_pos.2 hb0) d) := by
    funext n
    simp only [contMetricSample, LQGMetric.ContMetric.smul, ContinuousMap.smul_apply, smul_eq_mul]
    rw [hdp, hs n]
    exact (inv_mul_cancel_left₀ hb0.ne' _).symm
  have hdec : canonMetricDecoder 𝔇₀ α₀ (alphaCanon α₀ hC ω) =
      (LQGMetric.ContMetric.smul b⁻¹ (inv_pos.2 hb0) d).1 := by
    unfold canonMetricDecoder
    rw [hsample, contMetricOfSample_contMetricSample]
  intro u v
  rw [hdec]
  simp only [LQGMetric.ContMetric.smul, ContinuousMap.smul_apply, smul_eq_mul, hd]
  exact (mul_inv_cancel_left₀ hb0.ne' _).symm

end HarmonicBalls
