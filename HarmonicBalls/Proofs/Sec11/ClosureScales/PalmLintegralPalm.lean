import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmTestIdentity
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmPairingMeasurable
import HarmonicBalls.Proofs.Sec11.ClosureScales.MarkedComparison

/-! # Route (A), Step M: the Palm identity in lintegral form

For nonnegative test data (`ψ ≥ 0` bounded continuous on `ℝ^k`, `η ≥ 0` in `C_c(B₁)`), the Palm identity of
`palm_test_identity` holds with lintegrals: the left side integrates `ψ(hC φ)` against the marked mass, the right side
the shifted expectations. This is the form used to pass to indicators of open sets.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The shifted expectation `z ↦ E[ψ(hC φ + ∫ dmsShift_z φ)]` is measurable in the centre `z`. -/
theorem measurable_shifted_expectation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} {φ : Fin k → ℂ → ℝ} (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ψ : (Fin k → ℝ) → ℝ}
    (hψ : Continuous ψ) :
    Measurable fun z : ℂ => ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P := by
  have hjoint : Measurable fun p : ℂ × Ω =>
      ψ (fun j => hC p.2 (φ j) + ∫ x, dmsShift γ p.1 x * φ j x) := by
    refine hψ.measurable.comp (Measurable.of_eval fun j => ?_)
    exact ((hG.measurable_pairing (φ j) (hφ j)).comp measurable_snd).add
      ((measurable_integral_dmsShift γ (hφ j).1.continuous).comp measurable_fst)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

/-- The Palm identity (`palm_test_identity`) in lintegral form, for nonnegative test data. -/
theorem lintegral_palm_test {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {η : ℂ → ℝ} (hη : Continuous η) (hηs : HasCompactSupport η) (hη0 : ∀ z, 0 ≤ η z)
    (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) {k : ℕ} {φ : Fin k → ℂ → ℝ}
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ψ : (Fin k → ℝ) → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * (∫⁻ z, ENNReal.ofReal (η z) ∂(μ ω)) ∂P =
      ∫⁻ z, ENNReal.ofReal (η z) *
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) := by
  have hpalm := palm_test_identity hG γ hμ hU hη hηs hη0 htsupp φ hφ ψ hψ C hψC
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (hcirc ω) (μ ω) := by
    have h0 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hμ
    filter_upwards [h0] with ω hω
    rwa [fieldCircleAverage_zero] at hω
  have hint : Integrable (fun ω => ∫ z, η z ∂(μ ω)) P :=
    integrable_lqgMeasure_test_of_nonneg γ hG hμ hη hηs hη0 htsupp
  have hXm : ∀ j, Measurable (fun ω => hC ω (φ j)) := fun j => hG.measurable_pairing (φ j) (hφ j)
  have hψX : Measurable fun ω => ψ (fun j => hC ω (φ j)) :=
    hψ.measurable.comp (Measurable.of_eval fun j => hXm j)
  have hFC : ∀ ω, |ψ (fun j => hC ω (φ j))| ≤ C := fun ω => hψC _
  have hFint : Integrable (fun ω => ψ (fun j => hC ω (φ j)) * ∫ z, η z ∂(μ ω)) P :=
    integrable_bdd_mul hψX hFC hint
  have hF0 : 0 ≤ᵐ[P] (fun ω => ψ (fun j => hC ω (φ j)) * ∫ z, η z ∂(μ ω)) :=
    ae_of_all _ fun ω => mul_nonneg (hψ0 _) (integral_nonneg fun z => hη0 z)
  -- left side: the marked mass against `ψ(hC φ)` is the Bochner integral, a.e.
  have hL : ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * (∫⁻ z, ENNReal.ofReal (η z) ∂(μ ω)) ∂P =
      ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j)) * ∫ z, η z ∂(μ ω)) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hμ'] with ω hω
    have := hω.isLocallyFiniteMeasure
    have hηint : Integrable η (μ ω) := hη.integrable_of_hasCompactSupport hηs
    rw [← ofReal_integral_eq_lintegral_ofReal hηint (ae_of_all _ hη0),
      ← ENNReal.ofReal_mul (hψ0 _)]
  -- the shifted expectations
  have hR_inner : ∀ z : ℂ,
      ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P =
        ENNReal.ofReal (∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P) := by
    intro z
    have hm : Measurable fun ω => ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) :=
      hψ.measurable.comp (Measurable.of_eval fun j => (hXm j).add_const _)
    have hi : Integrable (fun ω => ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) P :=
      (integrable_const C).mono' hm.aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hψC _)
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => hψ0 _)]
  have hRsimp : ∀ z : ℂ,
      ENNReal.ofReal (η z) * ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P =
        ENNReal.ofReal (η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P) := by
    intro z
    rw [hR_inner z, ← ENNReal.ofReal_mul (hη0 z)]
  -- the right side is integrable in `z`
  have hGmeas : Measurable fun z : ℂ =>
      η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P :=
    hη.measurable.mul (measurable_shifted_expectation hG γ hφ hψ)
  have hGint : Integrable (fun z : ℂ =>
      η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P) (volume : Measure ℂ) := by
    have hηi : Integrable η (volume : Measure ℂ) := hη.integrable_of_hasCompactSupport hηs
    refine (hηi.const_mul C).mono' hGmeas.aestronglyMeasurable (ae_of_all _ fun z => ?_)
    have hI : |∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P| ≤ C := by
      have h := norm_integral_le_of_norm_le_const (μ := P) (C := C)
        (f := fun ω => ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x))
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]
          exact hψC _)
      simpa [Real.norm_eq_abs] using h
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hη0 z), mul_comm C]
    exact mul_le_mul_of_nonneg_left hI (hη0 z)
  have hG0 : 0 ≤ᵐ[(volume : Measure ℂ)] (fun z : ℂ =>
      η z * ∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P) :=
    ae_of_all _ fun z => mul_nonneg (hη0 z) (integral_nonneg fun ω => hψ0 _)
  rw [hL, lintegral_congr (fun z => hRsimp z), ← ofReal_integral_eq_lintegral_ofReal hFint hF0,
    ← ofReal_integral_eq_lintegral_ofReal hGint hG0, hpalm]

end HarmonicBalls

end
