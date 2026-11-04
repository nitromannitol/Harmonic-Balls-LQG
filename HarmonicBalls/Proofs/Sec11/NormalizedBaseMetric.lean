import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift
import HarmonicBalls.Proofs.Sec2.AffineField
import HarmonicBalls.Steps.Sec11.WeylScalingOrder

/-! # Normalization of the whole-plane LQG base metric -/

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- The affine pairing normalized by a circle average recovers the coordinate
change pairing after adding the circle-average and logarithmic constants. -/
theorem affinePairing_add_normalization {Ω : Type*}
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    {k : ℝ} (hk : 0 < k) (q : ℝ) (ω : Ω) :
    addFunPairing (affinePairing hC hcirc (k : ℂ) 0 ω)
        (fun _ => hcirc ω k 0 + q * Real.log k) =
      addFunPairing (affinePullbackPairing (hC ω) k 0)
        (fun _ => q * Real.log k) := by
  funext φ
  simp only [addFunPairing, affinePairing, affinePullbackPairing, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hk, sub_zero, integral_const_mul]
  ring

/-- The normalized affine whole-plane field has a base metric equal to a
positive random multiple of the geometrically dilated original base metric.
The affine-invariance hypothesis is staged pending source checking. -/
theorem IsWholePlaneGFF.ae_normalized_affine_baseMetric
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {k : ℝ} (hk : 0 < k) :
    ∀ᵐ ω ∂P, ∀ u v,
      𝔇 (affinePairing hC hcirc (k : ℂ) 0 ω) u v =
        Real.exp (-ξ * (hcirc ω k 0 + lqgQ γ * Real.log k)) *
          𝔇 (hC ω) (k • u) (k • v) := by
  let H := affinePairing hC hcirc (k : ℂ) 0
  let C := affineCircle hcirc (k : ℂ) 0
  have hGFF : IsWholePlaneGFF P H C :=
    hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  let f : Ω → ℂ → ℝ := fun ω _ => hcirc ω k 0 + lqgQ γ * Real.log k
  have hf : ∀ ω, Continuous (f ω) := fun _ => continuous_const
  have hfm : ∀ x, Measurable fun ω => f ω x := fun _ =>
    (h.measurable_circle k 0 hk).add measurable_const
  have hs := ae_wholePlane_weylScaling_shift P γ ξ H C 𝔇 h𝔇 hGFF f hf hfm
  have hbase := h𝔇.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => 0) h
    (by intro ω; fun_prop) (by intro x; fun_prop)
  have hzero : ∀ T : (ℂ → ℝ) → ℝ, addFunPairing T (fun _ => 0) = T := by
    intro T
    funext φ
    simp [addFunPairing]
  filter_upwards [hs, hbase.ae_isEuclideanLengthMetric, hbase.coordChange k hk 0] with ω hs hb hcoord
  simp only [hzero] at hb hcoord
  intro u v
  have hnorm : 0 ≤ 𝔇 (H ω) u v := by
    have htri := hs.1.triangle u v u
    rw [hs.1.self_eq_zero, hs.1.symm v u] at htri
    linarith
  have horig : 0 ≤ 𝔇 (hC ω) (k • u) (k • v) := by
    have htri := hb.triangle (k • u) (k • v) (k • u)
    rw [hb.self_eq_zero, hb.symm (k • v) (k • u)] at htri
    linarith
  have hcoord' : 𝔇 (hC ω) (k • u) (k • v) =
      𝔇 (addFunPairing (H ω) (f ω)) u v := by
    rw [affinePairing_add_normalization hC hcirc hk (lqgQ γ) ω]
    simpa only [Complex.real_smul, add_zero] using hcoord u v
  have hcost := hs.2.2.2.1 u v
  have hcost' : ENNReal.ofReal (𝔇 (hC ω) (k • u) (k • v)) =
      ENNReal.ofReal (Real.exp (ξ * (hcirc ω k 0 + lqgQ γ * Real.log k))) *
        ENNReal.ofReal (𝔇 (H ω) u v) := by
    rw [hcoord', hcost]
    have hw := weylScaling_add_const (𝔇 (H ω)) ξ
      (hcirc ω k 0 + lqgQ γ * Real.log k) 0 u v
    simp only [Pi.zero_apply, zero_add] at hw
    rw [hw, hs.2.2.1 u v]
  have hreal := congrArg ENNReal.toReal hcost'
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal horig,
    ENNReal.toReal_ofReal (Real.exp_nonneg _), ENNReal.toReal_ofReal hnorm] at hreal
  rw [hreal, ← mul_assoc, ← Real.exp_add]
  simp only [show -ξ * (hcirc ω k 0 + lqgQ γ * Real.log k) +
      ξ * (hcirc ω k 0 + lqgQ γ * Real.log k) = 0 by ring,
    Real.exp_zero, one_mul]
  rfl

#print axioms affinePairing_add_normalization
#print axioms IsWholePlaneGFF.ae_normalized_affine_baseMetric

end HarmonicBalls
