import HarmonicBalls.FirstPass.S11s.Covariance
import HarmonicBalls.FirstPass.S11v.DilOpCoord
import HarmonicBalls.FirstPass.S11v.Decoders
import HarmonicBalls.FirstPass.S11v.Affine

/-!
# B1 covariance of the decoders without pathwise homogeneity (fp-S11v, operator note 01:44 UTC, §4)

`ae_covariance_canonical` (S11s/Covariance.lean) uses `hhom : ∀ᵐ ω, PairingHomogeneous (hC ω)` only to rewrite
`dilOp (alphaCanon α hC ω)` as `alphaCanon α (normDilatePairing …) ω` pointwise. Here that identity is replaced by
its decoded form: `ae_dilOp_alphaCanon_apply_eq` (S11v/DilOpCoord.lean) gives coordinatewise almost sure equality, and
`ae_decoders_eq_of_coordwise_ae_eq` (S11v/Decoders.lean) turns it into almost sure equality of `K` and `d` at the two
canonical fields. The decoders are taken as a kernel `K` with locally finite values and a measurable metric map `d`
(the measurable decoder hypotheses of `LQGCanonicalDecodersMeasurableExistStmt`). The affine invariance `WholePlaneGFFAffineInvariance` is the theorem `wholePlaneGFFAffineInvariance_derived`
(S11v/Affine.lean), so no affine hypothesis is taken.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal

/-- **B1 covariance of the decoders, without `hhom`.** Almost surely there are `a, b > 0` with
`K (dilOp L) = a • (K L).map (· / (1/2))` and `d (dilOp L) (u, v) = b · d L (u/2, v/2)` for `L = alphaCanon α hC ω`. -/
theorem ae_covariance_canonical_dec {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ α : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {D : Ω → ℂ → ℂ → ℝ} (hD : IsLQGMetricOfField P γ ξ α hC D)
    (K : Kernel S11n.CanonSpace ℂ) (hKf : ∀ L, IsFiniteMeasureOnCompacts (K L))
    (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (hd : Measurable d)
    (hid : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ α (fun L => K L) (fun L x y => d L (x, y))) :
    ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      K (dilOp (alphaCanon α hC ω))
          = ENNReal.ofReal a • (K (alphaCanon α hC ω)).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ∧
      ∀ u v : ℂ, d (dilOp (alphaCanon α hC ω)) (u, v)
          = b * d (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := by
  have hG' := isWholePlaneGFF_affinePullback hG (wholePlaneGFFAffineInvariance_derived P hC hcirc)
  have hμ' := ae_isLQGMeasureOfField_affinePullback P hγ hG hμ
  have hD' := ae_isLQGMetricOfField_affinePullback P hG hD
  have hid1 := hid Ω P hC hcirc μ D hG hμ hD
  have hid2 := hid Ω P _ _ _ _ hG' hμ' hD'
  have hdec := ae_decoders_eq_of_coordwise_ae_eq
    (X := fun ω => dilOp (alphaCanon α hC ω))
    (Y := fun ω => alphaCanon α (fun ω' => normDilatePairing (hC ω') (hcirc ω' (1 / 2) 0) (1 / 2)) ω)
    (fun i => ae_dilOp_alphaCanon_apply_eq hG α (fun ω => hcirc ω (1 / 2) 0) i) K hKf d hd
  filter_upwards [hid1, hid2, hdec] with ω h1 h2 hdω
  obtain ⟨hKω, hdω'⟩ := hdω
  obtain ⟨a₀, b₀, ha₀, hb₀, hμω, hDω⟩ := h1
  obtain ⟨aT, bT, haT, hbT, hmuT, hDT⟩ := h2
  rw [← hKω] at hmuT
  -- measure: `e • (μ ω).map f = aT • K (dilOp L)` and `μ ω = a₀ • K L`
  have hmeasure : K (dilOp (alphaCanon α hC ω))
      = ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω)) (1 / 2))) * a₀ / aT)
        • (K (alphaCanon α hC ω)).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := by
    rw [hμω, Measure.map_smul, smul_smul, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at hmuT
    exact measure_eq_div_smul_of_ofReal_smul haT hmuT.symm
    exact (by fun_prop : Measurable (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ))).aemeasurable
  -- metric: the decoded identity `d (dilOp L) = d L'` transports the pulled-back metric to `d (dilOp L)`
  rw [← hdω'] at hDT
  have hmetric : ∀ u v : ℂ, d (dilOp (alphaCanon α hC ω)) (u, v)
      = Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)))) * b₀ / bT
        * d (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := by
    intro u v
    have h1 := hDT u v
    rw [hDω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)] at h1
    have h2 : bT * d (dilOp (alphaCanon α hC ω)) (u, v)
        = Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
          * b₀ * d (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v) := by
      rw [← h1]
      ring
    calc d (dilOp (alphaCanon α hC ω)) (u, v)
        = (bT * d (dilOp (alphaCanon α hC ω)) (u, v)) / bT := (mul_div_cancel_left₀ _ hbT.ne').symm
      _ = (Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
            * b₀ * d (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u, ((1 / 2 : ℝ) : ℂ) * v)) / bT := by
          rw [h2]
      _ = _ := by ring
  refine ⟨Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω)) (1 / 2))) * a₀ / aT,
    Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)))) * b₀ / bT,
    div_pos (mul_pos (Real.exp_pos _) ha₀) haT, div_pos (mul_pos (Real.exp_pos _) hb₀) hbT,
    hmeasure, hmetric⟩

end HarmonicBalls
