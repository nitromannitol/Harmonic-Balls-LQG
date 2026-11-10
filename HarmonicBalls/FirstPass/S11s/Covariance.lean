import HarmonicBalls.FirstPass.S11s.Transfer
import HarmonicBalls.FirstPass.S11n
import HarmonicBalls.FirstPass.S11i.MixingCanonical
import HarmonicBalls.FirstPass.S11i.AlphaCanonical

/-!
# B1, part A: covariance of the canonical decoders on realizations (fp-S11s-11-13-B1-covariance)

Ruling section 3, part A (eqs. (7)-(11)), with `r = 1/2`. For a whole-plane GFF model `h = h^ℂ - α log|·|` with LQG
measure `μ` and LQG metric `D`, the pulled-back model `h̃` (pairing `normDilatePairing`, circle averages of `hcirc` at
scale `1/2`, see `WholePlaneGFFAffineInvariance`) has LQG measure and metric the constant multiples of `μ.map (· / (1/2))`
and of the dilated metric (`Transfer.lean`). Applying the frozen canonical identification `LQGCanonicalIdentificationStmt`
to both models, and using `dilOp_alphaCanon_eq` (`alphaCanon` of `h̃` is `dilOp` of `alphaCanon` of `h`), gives, almost
surely with `L = alphaCanon α hC ω`:
`Dμ (dilOp L) = a • (Dμ L).map (· / (1/2))` and `Dd (dilOp L) u v = b * Dd L ((1/2) u) ((1/2) v)`, `a, b > 0`.

Universe: the models are over `Ω : Type` (as required by `ae_weylScaling_affinePullback_background`), so the frozen
identification is used at universe `0`.

Input (caveat 1, PENDING TRUTH CHECK): `WholePlaneGFFAffineInvariance` (`Proposed/LQG.lean`) is a hypothesis `hAff`.
Input (GAP A): the a.s. homogeneity `PairingHomogeneous (hC ω)` is a hypothesis `hhom`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The pulled-back pairing of `WholePlaneGFFAffineInvariance` with `a = 1/2`, `b = 0` is `normDilatePairing` with
`s = h^ℂ_{1/2}(0)`; hence the pulled-back model is a whole-plane GFF (caveat 1 input `hAff`). -/
theorem isWholePlaneGFF_affinePullback {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) :
    IsWholePlaneGFF P (fun ω => normDilatePairing (hC ω) (hcirc ω (1 / 2) 0) (1 / 2))
      (fun ω ρ z => hcirc ω ((1 / 2 : ℝ) * ρ) (((1 / 2 : ℝ) : ℂ) * z) - hcirc ω (1 / 2) 0) := by
  have hn : ‖((1 / 2 : ℝ) : ℂ)‖ = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have key := hAff hG ((1 / 2 : ℝ) : ℂ) (by norm_num) 0
  simp only [hn, add_zero] at key
  have e1 : (fun ω => normDilatePairing (hC ω) (hcirc ω (1 / 2) 0) (1 / 2))
      = (fun ω φ => ((1 / 2 : ℝ) ^ 2)⁻¹ * hC ω (fun y => φ ((y - 0) / ((1 / 2 : ℝ) : ℂ)))
          - hcirc ω (1 / 2) 0 * ∫ x, φ x) := by
    funext ω φ
    simp only [normDilatePairing, hn]
  rw [e1]
  exact key

/-- Scalar algebra in `ℝ≥0∞`: if `c₀ • X = k₀ • M` with `c₀ > 0`, `k₀ ≥ 0`, then `X = (k₀ / c₀) • M`. -/
theorem measure_eq_div_smul_of_ofReal_smul {X M : Measure ℂ} {c₀ k₀ : ℝ} (hc : 0 < c₀)
    (h : ENNReal.ofReal c₀ • X = ENNReal.ofReal k₀ • M) :
    X = ENNReal.ofReal (k₀ / c₀) • M := by
  have hc0 : ENNReal.ofReal c₀ ≠ 0 := (ENNReal.ofReal_pos.mpr hc).ne'
  have hctop : ENNReal.ofReal c₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  calc X = ((ENNReal.ofReal c₀)⁻¹ * ENNReal.ofReal c₀) • X := by
        rw [ENNReal.inv_mul_cancel hc0 hctop, one_smul]
    _ = (ENNReal.ofReal c₀)⁻¹ • (ENNReal.ofReal c₀ • X) := by rw [smul_smul]
    _ = (ENNReal.ofReal c₀)⁻¹ • (ENNReal.ofReal k₀ • M) := by rw [h]
    _ = ENNReal.ofReal (k₀ / c₀) • M := by
        rw [smul_smul, ENNReal.ofReal_div_of_pos hc, ENNReal.div_eq_inv_mul]

/-- **B1, part A (a.s. covariance on realizations).** For a whole-plane GFF model over `Ω : Type` with LQG measure
`μ` and LQG metric `D` of `h = h^ℂ - α log|·|`, and frozen canonical decoders `Dμ`, `Dd` (`hid`), almost surely the
canonical field `L = alphaCanon α hC ω` satisfies `Dμ (dilOp L) = a • (Dμ L).map (· / (1/2))` and
`Dd (dilOp L) u v = b * Dd L (u/2) (v/2)` with constants `a, b > 0`. -/
theorem ae_covariance_canonical {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ α : ℝ} (hγ : 0 < γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hhom : ∀ᵐ ω ∂P, PairingHomogeneous (hC ω))
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {D : Ω → ℂ → ℂ → ℝ} (hD : IsLQGMetricOfField P γ ξ α hC D)
    {Dμ : S11n.CanonSpace → Measure ℂ} {Dd : S11n.CanonSpace → ℂ → ℂ → ℝ}
    (hid : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ α Dμ Dd) :
    ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp (alphaCanon α hC ω))
          = ENNReal.ofReal a • (Dμ (alphaCanon α hC ω)).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) ∧
      ∀ u v : ℂ, Dd (dilOp (alphaCanon α hC ω)) u v
          = b * Dd (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v) := by
  have hG' := isWholePlaneGFF_affinePullback hG hAff
  have hμ' := ae_isLQGMeasureOfField_affinePullback P hγ hG hμ
  have hD' := ae_isLQGMetricOfField_affinePullback P hG hD
  have hid1 := hid Ω P hC hcirc μ D hG hμ hD
  have hid2 := hid Ω P _ _ _ _ hG' hμ' hD'
  filter_upwards [hid1, hid2, hhom] with ω h1 h2 hω
  obtain ⟨a₀, b₀, ha₀, hb₀, hμω, hDω⟩ := h1
  obtain ⟨aT, bT, haT, hbT, hmuT, hDT⟩ := h2
  have hT : dilOp (alphaCanon α hC ω)
      = alphaCanon α (fun ω' => normDilatePairing (hC ω') (hcirc ω' (1 / 2) 0) (1 / 2)) ω :=
    dilOp_alphaCanon_eq α hC (fun ω' => hcirc ω' (1 / 2) 0) ω hω
  rw [← hT] at hmuT hDT
  -- measure: `e • (μ ω).map f = aT • Dμ (dilOp L)` and `μ ω = a₀ • Dμ L`
  have hmeasure : Dμ (dilOp (alphaCanon α hC ω))
      = ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω)) (1 / 2))) * a₀ / aT)
        • (Dμ (alphaCanon α hC ω)).map (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ)) := by
    rw [hμω, Measure.map_smul, smul_smul, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at hmuT
    exact measure_eq_div_smul_of_ofReal_smul haT hmuT.symm
    exact (by fun_prop : Measurable (fun w : ℂ => w / ((1 / 2 : ℝ) : ℂ))).aemeasurable
  -- metric: `eξ * D ω (u/2) (v/2) = bT * Dd (dilOp L) u v` and `D ω (u/2) (v/2) = b₀ * Dd L (u/2) (v/2)`
  have hmetric : ∀ u v : ℂ, Dd (dilOp (alphaCanon α hC ω)) u v
      = Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)))) * b₀ / bT
        * Dd (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v) := by
    intro u v
    have h1 := hDT u v
    rw [hDω (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)] at h1
    have h2 : bT * Dd (dilOp (alphaCanon α hC ω)) u v
        = Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
          * b₀ * Dd (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v) := by
      rw [← h1]
      ring
    calc Dd (dilOp (alphaCanon α hC ω)) u v
        = (bT * Dd (dilOp (alphaCanon α hC ω)) u v) / bT := (mul_div_cancel_left₀ _ hbT.ne').symm
      _ = (Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2))))
            * b₀ * Dd (alphaCanon α hC ω) (((1 / 2 : ℝ) : ℂ) * u) (((1 / 2 : ℝ) : ℂ) * v)) / bT := by
          rw [h2]
      _ = _ := by ring
  refine ⟨Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω)) (1 / 2))) * a₀ / aT,
    Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) (1 / 2) 0 + lqgQ γ * Real.log (1 / 2)))) * b₀ / bT,
    div_pos (mul_pos (Real.exp_pos _) ha₀) haT, div_pos (mul_pos (Real.exp_pos _) hb₀) hbT,
    hmeasure, hmetric⟩

end HarmonicBalls
