import HarmonicBalls.Proposed.PfefferMetricScaling

/-! # Deterministic exponent comparison for Pfeffer's background scaling (1.10)

This file consumes `PfefferBackgroundScaling`, which is Pfeffer's Proposition 1.9, equation (1.10) (arXiv:2104.04020v3,
p. 8), staged as a proposed input in `HarmonicBalls/Proposed/PfefferMetricScaling.lean`. That input is pending the
operator's source-check.

What is proved here. If the scaling constants satisfy `c_r = r ^ (ξ · lqgQ γ)` exactly, then the background exponent
`Q` in (1.10) equals `lqgQ γ`. The argument is elementary. For `0 < δ < 1` and `r > 0`, the ratio
`c_{δr}/c_r = δ^{ξ lqgQ γ}` is exact, so `log (c_{δr}/c_r) / log δ = ξ lqgQ γ` identically. Pfeffer's (1.10) says the same
quotient lies within any `η > 0` of `ξ Q` for all small `δ`. Letting `δ → 0` forces `ξ lqgQ γ = ξ Q`, and `ξ > 0` gives
`Q = lqgQ γ`. The proof uses only `r = 1`, so it does not need the uniformity in `r` of (1.10).

Not proved here (remaining targets, see `docs/campaign/audits/MetricExponentScaling.md`): that the LQG metric
`IsLQGMetric` lies in the class `IsPfefferWeakLQGMetric`; that its Axiom V constants can be taken exactly
`r ^ (ξ · lqgQ γ)`, i.e. the tightness of the normalized distances at the exact normalizers; and the physical
parameter correspondence that identifies the background charge `Q(ξ)` of (1.4) with the LQG parameter.

Credit: Leonardo Bonanno, whose whole-plane GFF construction underlies the field carriers
(`HarmonicBalls/Proposed/PfefferMetricScaling.lean`, credit line).
-/

namespace HarmonicBalls

open Filter Topology Set

/-- For a power law `c x = x ^ s` on `(0, ∞)`, the quotient `log (c (δ r) / c r) / log δ` equals `s` for
`0 < δ < 1` and `r > 0`. -/
theorem log_power_ratio_div_log {s δ r : ℝ} {c : ℝ → ℝ} (hc : ∀ x : ℝ, 0 < x → c x = x ^ s)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hr : 0 < r) :
    Real.log (c (δ * r) / c r) / Real.log δ = s := by
  have hlog : Real.log δ ≠ 0 := (Real.log_neg hδ0 hδ1).ne
  rw [hc (δ * r) (mul_pos hδ0 hr), hc r hr, Real.mul_rpow hδ0.le hr.le,
    mul_div_cancel_right₀ _ (Real.rpow_pos_of_pos hr s).ne', Real.log_rpow hδ0,
    mul_div_cancel_right₀ _ hlog]

/-- Exact asymptotic type of (1.10): if `c` is a power law with exponent `s`, and for every `η > 0` the quotient
`log (c (δ r) / c r) / log δ` lies within `η` of `a` for all small `δ > 0` and all `r > 0`, then `s = a`. -/
theorem exponent_eq_of_asymptotic_power {s a : ℝ} {c : ℝ → ℝ} (hc : ∀ x : ℝ, 0 < x → c x = x ^ s)
    (H : ∀ η : ℝ, 0 < η → ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ r : ℝ, 0 < r →
      |Real.log (c (δ * r) / c r) / Real.log δ - a| ≤ η) :
    s = a := by
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
  apply eq_of_forall_dist_le
  intro η hη
  obtain ⟨δ, hδ, hδI⟩ := ((H η hη).and hev).exists
  have h1 := hδ 1 one_pos
  rw [log_power_ratio_div_log hc hδI.1 hδI.2 one_pos] at h1
  rw [Real.dist_eq]
  exact h1

/-- Deterministic exponent identification. Let `ξ > 0`, and let `𝔇` be a weak LQG metric with parameter `ξ`
(Definition 1.6) on an instance `(Ω, P, hC, hcirc, f)` of the field `h = h^ℂ + f`. If `c` is a family of Axiom V scaling
constants for that instance with the exact normalization `c_r = r ^ (ξ · lqgQ γ)`, then the background charge of (1.10),
`Q`, equals `lqgQ γ`. -/
theorem background_charge_eq_lqgQ_of_power_scaling {ξ Q γ : ℝ} (hξ : 0 < ξ)
    (hPf : PfefferBackgroundScaling ξ Q) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsPfefferWeakLQGMetric ξ 𝔇)
    (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ) (hh : IsWholePlaneGFF P hC hcirc)
    (hf : ∀ ω, Continuous (f ω)) (hfm : ∀ x, Measurable fun ω => f ω x)
    {c : ℝ → ℝ} (hV : PfefferAxiomVScale P ξ 𝔇 hC hcirc f c)
    (hpow : ∀ x : ℝ, 0 < x → c x = x ^ (ξ * lqgQ γ)) :
    Q = lqgQ γ := by
  have H := hPf 𝔇 h𝔇 Ω P hC hcirc f hh hf hfm c hV
  have h1 : ξ * lqgQ γ = ξ * Q := exponent_eq_of_asymptotic_power hpow H
  exact (mul_left_cancel₀ hξ.ne' h1).symm

end HarmonicBalls
