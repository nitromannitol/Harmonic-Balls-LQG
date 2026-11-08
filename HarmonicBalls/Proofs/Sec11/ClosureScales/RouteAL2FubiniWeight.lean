import Mathlib

/-! # Route (A), C3 (random part): integrability of the covariance weight

For a field `Z : Ω × ℂ → ℝ` with uniform second-moment bounds `∫⁻ Z(·,z)² dP ≤ C` on a compact `K`, and a
continuous `ψ` supported in `K`, the weight `(z, z') ↦ ψ z * ψ z' * E[Z(·,z) Z(·,z')]` is integrable on
`volume ⊗ volume`. This is step (d) of the L²-Fubini identity `integral_sq_integral_eq_double_integral`
(RouteAL2FubiniIdentity.lean). The bound used is `|E[Z z Z z']| ≤ (E Z z² + E Z z'²)/2 ≤ C.toReal` on `K × K`
(pointwise AM–GM, no Cauchy–Schwarz), and the weight vanishes off `K × K`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Integrability of `(z, z') ↦ ψ z * ψ z' * E[Z(·,z) Z(·,z')]` on `volume ⊗ volume`. -/
theorem integrable_weight_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Z : Ω → ℂ → ℝ} (hZm : Measurable (fun p : Ω × ℂ => Z p.1 p.2))
    {K : Set ℂ} (hK : IsCompact K) {ψ : ℂ → ℝ} (hψc : Continuous ψ)
    (hψK : ∀ z, z ∉ K → ψ z = 0) {C : ℝ≥0∞} (hCt : C < ⊤)
    (hL2 : ∀ z ∈ K, ∫⁻ ω, ENNReal.ofReal (Z ω z ^ 2) ∂P ≤ C) :
    Integrable (fun p : ℂ × ℂ => ψ p.1 * ψ p.2 * ∫ ω, Z ω p.1 * Z ω p.2 ∂P)
      ((volume : Measure ℂ).prod volume) := by
  -- second moments of `Z(·, z)` for `z ∈ K`
  have hsqint : ∀ z ∈ K, Integrable (fun ω => Z ω z ^ 2) P := by
    intro z hz
    have hmz : Measurable (fun ω : Ω => Z ω z) := hZm.comp (measurable_id.prodMk measurable_const)
    refine ⟨(hmz.pow_const 2).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ ω, ‖Z ω z ^ 2‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (Z ω z ^ 2) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ C := hL2 z hz
      _ < ⊤ := hCt
  have hsq_le : ∀ z ∈ K, ∫ ω, Z ω z ^ 2 ∂P ≤ C.toReal := by
    intro z hz
    have h1 := ofReal_integral_eq_lintegral_ofReal (hsqint z hz) (ae_of_all _ fun ω => sq_nonneg _)
    have h2 : ENNReal.ofReal (∫ ω, Z ω z ^ 2 ∂P) ≤ C := by
      rw [h1]
      exact hL2 z hz
    exact (ENNReal.ofReal_le_iff_le_toReal hCt.ne).1 h2
  -- the covariance is bounded by `C.toReal` on `K × K`
  have hI : ∀ z ∈ K, ∀ z' ∈ K, |∫ ω, Z ω z * Z ω z' ∂P| ≤ C.toReal := by
    intro z hz z' hz'
    have hpt : ∀ ω, |Z ω z * Z ω z'| ≤ (Z ω z ^ 2 + Z ω z' ^ 2) / 2 := fun ω => by
      rw [abs_mul]
      nlinarith [sq_abs (Z ω z), sq_abs (Z ω z'), sq_nonneg (|Z ω z| - |Z ω z'|)]
    calc |∫ ω, Z ω z * Z ω z' ∂P| ≤ ∫ ω, |Z ω z * Z ω z'| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (Z ω z ^ 2 + Z ω z' ^ 2) / 2 ∂P :=
          integral_mono_of_nonneg (ae_of_all _ fun ω => abs_nonneg _)
            (((hsqint z hz).add (hsqint z' hz')).div_const 2) (ae_of_all _ hpt)
      _ = (∫ ω, Z ω z ^ 2 ∂P + ∫ ω, Z ω z' ^ 2 ∂P) / 2 := by
          rw [integral_div, integral_add (hsqint z hz) (hsqint z' hz')]
      _ ≤ C.toReal := by linarith [hsq_le z hz, hsq_le z' hz']
  -- boundedness of `ψ`
  obtain ⟨S, hS⟩ := hψc.bounded_above_of_compact_support
    (HasCompactSupport.intro hK fun z hz => hψK z hz)
  have hS' : ∀ z, |ψ z| ≤ S := fun z => by
    have := hS z
    rwa [Real.norm_eq_abs] at this
  have hS0 : 0 ≤ S := (abs_nonneg _).trans (hS' 0)
  -- measurability of the weight
  have hmeas2 : Measurable (fun q : (ℂ × ℂ) × Ω => Z q.2 q.1.1 * Z q.2 q.1.2) :=
    (hZm.comp (measurable_snd.prodMk measurable_fst.fst)).mul
      (hZm.comp (measurable_snd.prodMk measurable_fst.snd))
  have hIm : StronglyMeasurable (fun p : ℂ × ℂ => ∫ ω, Z ω p.1 * Z ω p.2 ∂P) :=
    hmeas2.stronglyMeasurable.integral_prod_right' (ν := P)
  have hgm : AEStronglyMeasurable (fun p : ℂ × ℂ => ψ p.1 * ψ p.2 * ∫ ω, Z ω p.1 * Z ω p.2 ∂P)
      ((volume : Measure ℂ).prod volume) :=
    (((hψc.measurable.comp measurable_fst).mul (hψc.measurable.comp measurable_snd)).mul
      hIm.measurable).aestronglyMeasurable
  -- integrable majorant: a constant on the compact set `K × K`
  have hG : Integrable ((K ×ˢ K).indicator (fun _ : ℂ × ℂ => S * S * C.toReal))
      ((volume : Measure ℂ).prod volume) := by
    refine (integrable_indicator_iff (hK.isClosed.measurableSet.prod hK.isClosed.measurableSet)).2 ?_
    exact integrableOn_const (hK.prod hK).measure_lt_top.ne
  refine hG.mono' hgm (ae_of_all _ fun p => ?_)
  show ‖ψ p.1 * ψ p.2 * ∫ ω, Z ω p.1 * Z ω p.2 ∂P‖ ≤ (K ×ˢ K).indicator (fun _ : ℂ × ℂ => S * S * C.toReal) p
  by_cases hp : p ∈ K ×ˢ K
  · rw [Set.indicator_of_mem hp, Real.norm_eq_abs, abs_mul, abs_mul]
    have h1 : |ψ p.1| ≤ S := hS' _
    have h2 : |ψ p.2| ≤ S := hS' _
    have h3 : |∫ ω, Z ω p.1 * Z ω p.2 ∂P| ≤ C.toReal := hI _ hp.1 _ hp.2
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hS0) h3 (abs_nonneg _) (mul_nonneg hS0 hS0)
  · rw [Set.indicator_of_notMem hp]
    have h0 : ψ p.1 * ψ p.2 = 0 := by
      by_cases h1 : p.1 ∈ K
      · have h2 : p.2 ∉ K := fun h2 => hp (Set.mk_mem_prod h1 h2)
        rw [hψK p.2 h2, mul_zero]
      · rw [hψK p.1 h1, zero_mul]
    simp [h0]

end HarmonicBalls

end
