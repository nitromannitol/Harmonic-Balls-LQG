import Mathlib
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleGaussianMoment
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleAverageJointMeasurable

/-! # Route (A), Palm identity: the first moment of the marked mass at scale ε

For the whole-plane GFF, `μ_ε(dz) = ε^(γ²/2) exp(γ h_ε(z)) dz` with `h_ε(z) = hcirc · ε z` the circle average at
radius `ε`. For a continuous compactly supported `η` and small `ε`, `E μ_ε(η) = ∫ η`.
The hypothesis `hdisk` says that the circles of radius `ε` about the points of `tsupport η` lie in the closed unit disk
(for small `ε` this holds because `tsupport η ⊆ B_1` is compact). Inputs: the Gaussian moment
(`integral_exp_circleAverage_eq`, CircleGaussianMoment.lean), the jointly measurable version
(`exists_measurable_circleAverage_version`, CircleAverageJointMeasurable.lean), Tonelli and Fubini.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped Classical

namespace HarmonicBalls

/-- **First moment of the marked mass**: `E ∫ η(z) ε^(γ²/2) exp(γ h_ε(z)) dz = ∫ η`. -/
theorem integral_marked_mass_eps_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε) (γ : ℝ) {η : ℂ → ℝ}
    (hη : Continuous η) (hηs : HasCompactSupport η)
    (hdisk : ∀ z ∈ tsupport η, ∀ x ∈ Metric.sphere z ε, ‖x‖ ≤ 1) :
    Integrable (fun ω => ∫ z, η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂(volume : Measure ℂ)) P ∧
    ∫ ω, ∫ z, η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂(volume : Measure ℂ) ∂P
      = ∫ z, η z ∂(volume : Measure ℂ) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ε ^ (γ ^ 2 / 2) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Real.exp (γ ^ 2 * (-Real.log ε) / 2) := ⟨_, rfl⟩
  have hcpos : 0 < c := by
    rw [hc]
    exact Real.rpow_pos_of_pos hε _
  have hKpos : 0 < K := by
    rw [hK]
    exact Real.exp_pos _
  have hcK : c * K = 1 := by
    rw [hc, hK, Real.rpow_def_of_pos hε, ← Real.exp_add]
    rw [show Real.log ε * (γ ^ 2 / 2) + γ ^ 2 * (-Real.log ε) / 2 = 0 by ring, Real.exp_zero]
  -- a jointly measurable version of the circle averages, equal to `hcirc` off a null set `N`
  obtain ⟨g, hgm, _, N, _, hN0, hgN⟩ := exists_measurable_circleAverage_version hG hε
  have hae : ∀ᵐ ω ∂P, ω ∉ N := ae_iff.2 (by simpa using hN0)
  -- the Gaussian moment at each point of the support
  have hIz : ∀ z ∈ tsupport η, Integrable (fun ω => Real.exp (γ * g ω z)) P := by
    intro z hz
    have hI : Integrable (fun ω => Real.exp (γ * hcirc ω ε z)) P := by
      by_contra hni
      have h2 := integral_exp_circleAverage_eq hG hε z (hdisk z hz) γ
      rw [integral_undef hni] at h2
      exact (Real.exp_pos _).ne h2
    refine hI.congr ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω z]
  have hKz : ∀ z ∈ tsupport η, ∫ ω, Real.exp (γ * g ω z) ∂P = K := by
    intro z hz
    rw [hK, ← integral_exp_circleAverage_eq hG hε z (hdisk z hz) γ]
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    rw [hgN ω hω z]
  have hmeasF : Measurable (fun p : Ω × ℂ => η p.2 * (c * Real.exp (γ * g p.1 p.2))) :=
    (hη.measurable.comp measurable_snd).mul
      (measurable_const.mul (Real.continuous_exp.measurable.comp (measurable_const.mul hgm)))
  -- pointwise in `z`: the lower Lebesgue integral of the modulus over the samples
  have hbound : ∀ z : ℂ, ∫⁻ ω, ‖η z * (c * Real.exp (γ * g ω z))‖ₑ ∂P
      ≤ ENNReal.ofReal (|η z| * c * K) := by
    intro z
    by_cases hz : z ∈ tsupport η
    · refine le_of_eq ?_
      calc ∫⁻ ω, ‖η z * (c * Real.exp (γ * g ω z))‖ₑ ∂P
          = ∫⁻ ω, ENNReal.ofReal (|η z| * c) * ENNReal.ofReal (Real.exp (γ * g ω z)) ∂P := by
            refine lintegral_congr fun ω => ?_
            rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_mul, abs_of_pos hcpos,
              abs_of_pos (Real.exp_pos _), ← mul_assoc,
              ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hcpos.le)]
        _ = ENNReal.ofReal (|η z| * c) * ∫⁻ ω, ENNReal.ofReal (Real.exp (γ * g ω z)) ∂P :=
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ENNReal.ofReal (|η z| * c) * ENNReal.ofReal K := by
            rw [← ofReal_integral_eq_lintegral_ofReal (hIz z hz)
              (ae_of_all _ fun ω => (Real.exp_pos _).le), hKz z hz]
        _ = ENNReal.ofReal (|η z| * c * K) :=
            (ENNReal.ofReal_mul (mul_nonneg (abs_nonneg _) hcpos.le)).symm
    · simp [image_eq_zero_of_notMem_tsupport hz]
  -- integrability on `P ⊗ volume` (Tonelli, then the pointwise bound)
  have hprod : Integrable (Function.uncurry fun (ω : Ω) (z : ℂ) => η z * (c * Real.exp (γ * g ω z)))
      (P.prod (volume : Measure ℂ)) := by
    refine ⟨hmeasF.aestronglyMeasurable, ?_⟩
    have hmeasN : AEMeasurable (fun p : Ω × ℂ => ‖η p.2 * (c * Real.exp (γ * g p.1 p.2))‖ₑ)
        (P.prod (volume : Measure ℂ)) :=
      hmeasF.enorm.aemeasurable
    have hint : Integrable (fun z => |η z| * c * K) (volume : Measure ℂ) :=
      (((hη.integrable_of_hasCompactSupport hηs).abs).mul_const c).mul_const K
    unfold HasFiniteIntegral
    calc ∫⁻ p, ‖Function.uncurry (fun (ω : Ω) (z : ℂ) => η z * (c * Real.exp (γ * g ω z))) p‖ₑ
          ∂(P.prod (volume : Measure ℂ))
        = ∫⁻ ω, ∫⁻ z, ‖η z * (c * Real.exp (γ * g ω z))‖ₑ ∂(volume : Measure ℂ) ∂P :=
          lintegral_prod _ hmeasN
      _ = ∫⁻ z, ∫⁻ ω, ‖η z * (c * Real.exp (γ * g ω z))‖ₑ ∂P ∂(volume : Measure ℂ) :=
          lintegral_lintegral_swap (f := fun ω z => ‖η z * (c * Real.exp (γ * g ω z))‖ₑ) hmeasN
      _ ≤ ∫⁻ z, ENNReal.ofReal (|η z| * c * K) ∂(volume : Measure ℂ) := lintegral_mono hbound
      _ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun z => mul_nonneg (mul_nonneg (abs_nonneg _) hcpos.le) hKpos.le)]
        exact ENNReal.ofReal_lt_top
  -- the inner expectation is `η z` (the Gaussian moment and `c K = 1`)
  have hinner : ∀ z : ℂ, ∫ ω, η z * (c * Real.exp (γ * g ω z)) ∂P = η z := by
    intro z
    by_cases hz : z ∈ tsupport η
    · rw [integral_const_mul, integral_const_mul, hKz z hz, hcK, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  -- Fubini, then the a.e. replacement of `hcirc` by its measurable version
  refine ⟨?_, ?_⟩
  · refine hprod.integral_prod_left.congr ?_
    filter_upwards [hae] with ω hω
    show ∫ z, η z * (c * Real.exp (γ * g ω z)) ∂(volume : Measure ℂ) = _
    rw [← hc]
    congr 1
    funext z
    rw [hgN ω hω z]
  calc ∫ ω, ∫ z, η z * (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) ∂(volume : Measure ℂ) ∂P
      = ∫ ω, ∫ z, η z * (c * Real.exp (γ * g ω z)) ∂(volume : Measure ℂ) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with ω hω
        rw [← hc]
        congr 1
        funext z
        rw [hgN ω hω z]
    _ = ∫ z, ∫ ω, η z * (c * Real.exp (γ * g ω z)) ∂P ∂(volume : Measure ℂ) :=
        integral_integral_swap hprod
    _ = ∫ z, η z ∂(volume : Measure ℂ) := integral_congr_ae (ae_of_all _ hinner)

end HarmonicBalls

end
