import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAL2Fubini
import HarmonicBalls.Proofs.Sec11.ClosureScales.RouteAL2FubiniWeight

/-! # Route (A), C3 (random part): the L²-Fubini identity for the pairing of a continuous field

For `Z : Ω × ℂ → ℝ` with continuous sample paths and uniform second moments on a compact `K`, and `ψ` continuous and
supported in `K`:
`E[(∫ Z(·, z) ψ(z) dz)²] = ∫∫ ψ(z) ψ(z') E[Z(·, z) Z(·, z')] dz dz'`.
This is the first step of the identity `∫ c(r, z) ψ(z) dz = hC(ψ_r)` a.s. (r8 l.504-642, "first in L²").
The integrability input is `integrable_abs_mul_sq_prod` (RouteAL2Fubini.lean).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Integrability of the triple product `(ω, (z, z')) ↦ Z(ω,z) ψ(z) Z(ω,z') ψ(z')` on `P ⊗ (dz ⊗ dz')`. -/
theorem integrable_triple_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℂ → ℝ} (hZm : Measurable (fun p : Ω × ℂ => Z p.1 p.2)) (hcont : ∀ ω, Continuous (Z ω))
    {K : Set ℂ} (hK : IsCompact K) {ψ : ℂ → ℝ} (hψc : Continuous ψ) (hψK : ∀ z, z ∉ K → ψ z = 0)
    {C : ℝ≥0∞} (hCt : C < ⊤) (hL2 : ∀ z ∈ K, ∫⁻ ω, ENNReal.ofReal (Z ω z ^ 2) ∂P ≤ C) :
    Integrable (fun q : Ω × (ℂ × ℂ) => (Z q.1 q.2.1 * ψ q.2.1) * (Z q.1 q.2.2 * ψ q.2.2))
      (P.prod ((volume : Measure ℂ).prod volume)) := by
  have hfi : ∀ ω, Integrable (fun z => Z ω z * ψ z) (volume : Measure ℂ) := fun ω =>
    ((hcont ω).mul hψc).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun z hz => by simp [hψK z hz])
  have hgi : ∀ ω, Integrable (fun z => |ψ z| * Z ω z ^ 2) (volume : Measure ℂ) := fun ω =>
    (hψc.abs.mul ((hcont ω).pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK fun z hz => by simp [hψK z hz])
  have hBi : Integrable (fun z => |ψ z|) (volume : Measure ℂ) :=
    hψc.abs.integrable_of_hasCompactSupport (HasCompactSupport.intro hK fun z hz => by simp [hψK z hz])
  have hsec := integrable_abs_mul_sq_prod hZm hcont hK hψc hψK hCt hL2
  have hA : Integrable (fun ω => ∫ y, |ψ y| * Z ω y ^ 2 ∂(volume : Measure ℂ)) P := by
    refine ((integrable_prod_iff hsec.aestronglyMeasurable).1 hsec).2.congr (ae_of_all _ fun ω => ?_)
    beta_reduce
    congr 1
    funext y
    exact Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (sq_nonneg _))
  have hm1 : Measurable (fun q : Ω × (ℂ × ℂ) => Z q.1 q.2.1 * ψ q.2.1) :=
    (hZm.comp (measurable_fst.prodMk measurable_snd.fst)).mul (hψc.measurable.comp measurable_snd.fst)
  have hm2 : Measurable (fun q : Ω × (ℂ × ℂ) => Z q.1 q.2.2 * ψ q.2.2) :=
    (hZm.comp (measurable_fst.prodMk measurable_snd.snd)).mul (hψc.measurable.comp measurable_snd.snd)
  have hmF : Measurable (fun q : Ω × (ℂ × ℂ) => (Z q.1 q.2.1 * ψ q.2.1) * (Z q.1 q.2.2 * ψ q.2.2)) :=
    hm1.mul hm2
  -- for each `ω`, the double integral of the modulus is at most `(∫ |ψ| Z(ω,·)²)(∫ |ψ|)` (AM–GM)
  have hF : ∀ ω, ∫ p : ℂ × ℂ, ‖(Z ω p.1 * ψ p.1) * (Z ω p.2 * ψ p.2)‖ ∂((volume : Measure ℂ).prod volume)
      ≤ (∫ z, |ψ z| * Z ω z ^ 2 ∂(volume : Measure ℂ)) * ∫ z, |ψ z| ∂(volume : Measure ℂ) := by
    intro ω
    have hbd : ∀ p : ℂ × ℂ, ‖(Z ω p.1 * ψ p.1) * (Z ω p.2 * ψ p.2)‖
        ≤ (|ψ p.1| * Z ω p.1 ^ 2 * |ψ p.2| + |ψ p.1| * (|ψ p.2| * Z ω p.2 ^ 2)) / 2 := by
      intro p
      have key : |Z ω p.1| * |Z ω p.2| ≤ (Z ω p.1 ^ 2 + Z ω p.2 ^ 2) / 2 := by
        nlinarith [sq_abs (Z ω p.1), sq_abs (Z ω p.2), sq_nonneg (|Z ω p.1| - |Z ω p.2|)]
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left key (mul_nonneg (abs_nonneg (ψ p.1)) (abs_nonneg (ψ p.2)))]
    have hbi : Integrable
        (fun p : ℂ × ℂ => (|ψ p.1| * Z ω p.1 ^ 2 * |ψ p.2| + |ψ p.1| * (|ψ p.2| * Z ω p.2 ^ 2)) / 2)
        ((volume : Measure ℂ).prod volume) :=
      (((hgi ω).mul_prod hBi).add (hBi.mul_prod (hgi ω))).div_const 2
    have e1 : ∫ p : ℂ × ℂ, |ψ p.1| * Z ω p.1 ^ 2 * |ψ p.2| ∂((volume : Measure ℂ).prod volume)
        = (∫ z, |ψ z| * Z ω z ^ 2 ∂(volume : Measure ℂ)) * ∫ z, |ψ z| ∂(volume : Measure ℂ) :=
      integral_prod_mul (fun z => |ψ z| * Z ω z ^ 2) (fun z => |ψ z|)
    have e2 : ∫ p : ℂ × ℂ, |ψ p.1| * (|ψ p.2| * Z ω p.2 ^ 2) ∂((volume : Measure ℂ).prod volume)
        = (∫ z, |ψ z| ∂(volume : Measure ℂ)) * ∫ z, |ψ z| * Z ω z ^ 2 ∂(volume : Measure ℂ) :=
      integral_prod_mul (fun z => |ψ z|) (fun z => |ψ z| * Z ω z ^ 2)
    calc ∫ p : ℂ × ℂ, ‖(Z ω p.1 * ψ p.1) * (Z ω p.2 * ψ p.2)‖ ∂((volume : Measure ℂ).prod volume)
        ≤ ∫ p : ℂ × ℂ, (|ψ p.1| * Z ω p.1 ^ 2 * |ψ p.2| + |ψ p.1| * (|ψ p.2| * Z ω p.2 ^ 2)) / 2
            ∂((volume : Measure ℂ).prod volume) :=
          integral_mono_of_nonneg (ae_of_all _ fun p => norm_nonneg _) hbi (ae_of_all _ hbd)
      _ = (∫ z, |ψ z| * Z ω z ^ 2 ∂(volume : Measure ℂ)) * ∫ z, |ψ z| ∂(volume : Measure ℂ) := by
          rw [integral_div, integral_add ((hgi ω).mul_prod hBi) (hBi.mul_prod (hgi ω)), e1, e2]
          ring
  refine (integrable_prod_iff hmF.aestronglyMeasurable).2 ⟨ae_of_all _ fun ω => ?_, ?_⟩
  · exact (hfi ω).mul_prod (hfi ω)
  · refine Integrable.mono' (hA.mul_const (∫ z, |ψ z| ∂(volume : Measure ℂ))) ?_ (ae_of_all _ fun ω => ?_)
    · exact (hmF.norm.stronglyMeasurable.integral_prod_right'
        (ν := (volume : Measure ℂ).prod volume)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun p => norm_nonneg _)]
      exact hF ω

/-- The L²-Fubini identity: `E[(∫ Z(·,z) ψ(z) dz)²] = ∫∫ ψ(z) ψ(z') E[Z(·,z) Z(·,z')] dz dz'`. -/
theorem integral_sq_integral_eq_double_integral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → ℂ → ℝ} (hZm : Measurable (fun p : Ω × ℂ => Z p.1 p.2))
    (hcont : ∀ ω, Continuous (Z ω)) {K : Set ℂ} (hK : IsCompact K) {ψ : ℂ → ℝ} (hψc : Continuous ψ)
    (hψK : ∀ z, z ∉ K → ψ z = 0) {C : ℝ≥0∞} (hCt : C < ⊤)
    (hL2 : ∀ z ∈ K, ∫⁻ ω, ENNReal.ofReal (Z ω z ^ 2) ∂P ≤ C) :
    ∫ ω, (∫ z, Z ω z * ψ z) ^ 2 ∂P
      = ∫ z, ∫ z', ψ z * ψ z' * ∫ ω, Z ω z * Z ω z' ∂P := by
  set μ : Measure ℂ := volume with hμ
  have hF := integrable_triple_prod hZm hcont hK hψc hψK hCt hL2
  -- step a: the square of a one-dimensional integral is a double integral (for each `ω`)
  have ha : ∀ ω, (∫ z, Z ω z * ψ z) ^ 2
      = ∫ p, (Z ω p.1 * ψ p.1) * (Z ω p.2 * ψ p.2) ∂(μ.prod μ) := by
    intro ω
    have hfi : Integrable (fun z => Z ω z * ψ z) μ := by
      have hc : Continuous (fun z => Z ω z * ψ z) := (hcont ω).mul hψc
      exact hc.integrable_of_hasCompactSupport
        (HasCompactSupport.intro hK (fun z hz => by simp [hψK z hz]))
    rw [sq, integral_prod_mul (μ := μ) (ν := μ) (fun z => Z ω z * ψ z) (fun z => Z ω z * ψ z)]
  -- step b: exchange the integral over `ω` with the double integral over `(z, z')`
  have hb : ∫ ω, (∫ z, Z ω z * ψ z) ^ 2 ∂P
      = ∫ p, ∫ ω, (Z ω p.1 * ψ p.1) * (Z ω p.2 * ψ p.2) ∂P ∂(μ.prod μ) := by
    simp_rw [ha]
    exact integral_integral_swap hF
  -- step c: pull out the deterministic weights
  have hc : ∀ p : ℂ × ℂ, ∫ ω, (Z ω p.1 * ψ p.1) * (Z ω p.2 * ψ p.2) ∂P
      = ψ p.1 * ψ p.2 * ∫ ω, Z ω p.1 * Z ω p.2 ∂P := by
    intro p
    rw [← integral_const_mul]
    congr 1
    funext ω
    ring
  -- step d: the weights are integrable on `μ ⊗ μ` (bounded and compactly supported)
  have hG : Integrable (fun p : ℂ × ℂ => ψ p.1 * ψ p.2 * ∫ ω, Z ω p.1 * Z ω p.2 ∂P) (μ.prod μ) :=
    integrable_weight_prod hZm hK hψc hψK hCt hL2
  calc ∫ ω, (∫ z, Z ω z * ψ z) ^ 2 ∂P
      = ∫ p, ∫ ω, (Z ω p.1 * ψ p.1) * (Z ω p.2 * ψ p.2) ∂P ∂(μ.prod μ) := hb
    _ = ∫ p : ℂ × ℂ, ψ p.1 * ψ p.2 * ∫ ω, Z ω p.1 * Z ω p.2 ∂P ∂(μ.prod μ) :=
        integral_congr_ae (ae_of_all _ fun p => hc p)
    _ = ∫ z, ∫ z', ψ z * ψ z' * ∫ ω, Z ω z * Z ω z' ∂P ∂μ := integral_prod _ hG

end HarmonicBalls

end
