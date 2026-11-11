import HarmonicBalls.FirstPass.S11s.Transfer
import HarmonicBalls.FirstPass.S11q

/-!
# Dyadic zoom of the B1 transfer

The affine pullback of a whole-plane GFF model at scale `R`: `h̃_R(ρ, z) = h(Rρ, Rz) - h_R(0)` (the field of
`dilatedCircleAverage`, Duplantier-Sheffield scaling, ruling eqs. (9)-(11) of `S11s/Transfer.lean` with `R` in place of `1/2`).

* `ae_isLQGMeasureOfField_dyadicZoom`: for `R = 2^k`, `k : ℕ`, the LQG measure of `h̃_R` is
  `e^{-γ c_R} · μ.map (· / R)` almost surely (`isLQGLimit_dilate_dyadic`, FirstPass/S11q.lean, is the input). The measure
  limit needs the dyadic scales, so only `R = 2^k` is covered here.
* `ae_isLQGMetricOfField_zoom`: for every `R > 0` the LQG metric of the pulled-back pairing is `e^{-ξ c'_R} · D(R·, R·)`
  almost surely (`ae_weylScaling_affinePullback_background`, FirstPass/S11q/Metric.lean, is the input).

The proofs are those of `S11s/Transfer.lean` (`R = 1/2`) with `R` general. No literature input is added; `Ω : Type` is required
by `ae_weylScaling_affinePullback_background`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- **Measure, dyadic zoom.** For `k : ℕ` the pulled-back field `h̃_k(ρ, z) = h(2^k ρ, 2^k z) - h_{2^k}(0)` has LQG measure
`e^{-γ c_k} · μ.map (· / 2^k)` almost surely, with `c_k = dilationConstant γ (fieldCircleAverage α (hcirc ω)) (2^k)`. -/
theorem ae_isLQGMeasureOfField_dyadicZoom {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ α : ℝ}
    (hγ : 0 < γ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) (k : ℕ) :
    IsLQGMeasureOfField P γ α
      (fun ω ρ z => hcirc ω (((2 : ℝ) ^ k) * ρ) ((((2 : ℝ) ^ k : ℝ) : ℂ) * z) - hcirc ω ((2 : ℝ) ^ k) 0)
      (fun ω => ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ (fieldCircleAverage α (hcirc ω)) ((2 : ℝ) ^ k))))
        • (μ ω).map (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ))) := by
  unfold IsLQGMeasureOfField IsLQGMeasure at hμ ⊢
  filter_upwards [hμ, hG.ae_continuousOn_circle] with ω hω hcont
  refine isLQGLimit_congr_pos (fun ε hε z => ?_)
    (isLQGLimit_dilate_dyadic hω hγ k (fun r hr => measurable_fieldCircleAverage hcont hr))
  exact fieldCircleAverage_affinePullback α (hcirc ω) (by positivity : (0 : ℝ) < (2 : ℝ) ^ k) hε.ne' z

/-- **Metric, zoom.** For every `R > 0` the LQG metric of the pulled-back pairing `normDilatePairing (hC ω) (h_R(0)) R` is
`e^{-ξ c'_R} · D(R·, R·)` almost surely, `c'_R = h_R(0) - α log R + Q log R` (paper eqs. (10)-(11) with `R` in place of `1/2`). -/
theorem ae_isLQGMetricOfField_zoom {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) {D : Ω → ℂ → ℂ → ℝ}
    (hD : IsLQGMetricOfField P γ ξ α hC D) {R : ℝ} (hR : 0 < R) :
    IsLQGMetricOfField P γ ξ α
      (fun ω => normDilatePairing (hC ω) (hcirc ω R 0) R)
      (fun ω u v => Real.exp (-(ξ * (fieldCircleAverage α (hcirc ω) R 0 + lqgQ γ * Real.log R)))
        * D ω ((R : ℂ) * u) ((R : ℂ) * v)) := by
  obtain ⟨𝔇, h𝔇, hDae⟩ := hD
  have hc : Measurable (fun ω => hcirc ω R 0 + lqgQ γ * Real.log R) :=
    (hG.measurable_circle R 0 hR).add_const _
  refine ⟨𝔇, h𝔇, ?_⟩
  filter_upwards [hDae, ae_weylScaling_affinePullback_background hG 𝔇 h𝔇 (R := R) hR
    (fun ω => hcirc ω R 0 + lqgQ γ * Real.log R) hc α] with ω hω hW
  have hP : addFunPairing (affinePullbackPairing (hC ω) R 0)
      (fun _ => lqgQ γ * Real.log R - (hcirc ω R 0 + lqgQ γ * Real.log R))
      = normDilatePairing (hC ω) (hcirc ω R 0) R := by
    rw [normDilatePairing_eq_addFunPairing]
    congr 1
    funext x
    ring
  have hexp : -(ξ * ((hcirc ω R 0 + lqgQ γ * Real.log R) - α * Real.log R))
      = -(ξ * (fieldCircleAverage α (hcirc ω) R 0 + lqgQ γ * Real.log R)) := by
    have h0 : fieldCircleAverage α (hcirc ω) R 0 = hcirc ω R 0 - α * Real.log R := by
      unfold fieldCircleAverage
      rw [circleAverage_log_norm_zero hR.ne']
    rw [h0]
    ring
  rw [hP] at hW
  intro u v
  refine ⟨mul_nonneg (Real.exp_nonneg _) (hω ((R : ℂ) * u) ((R : ℂ) * v)).1, ?_⟩
  rw [hW u v, ENNReal.ofReal_mul (Real.exp_nonneg _),
    (hω ((R : ℂ) * u) ((R : ℂ) * v)).2, hexp]

end HarmonicBalls
