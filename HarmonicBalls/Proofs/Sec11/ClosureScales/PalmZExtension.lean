import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmLintegralPalm
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmInnerApprox

/-! # Route (A), Step M: the Palm identity in lintegral form for open sets of marked points

For an open set `W ⊆ ℂ`, the marked point `z` ranges over `W ∩ B₁`. The indicator of `W ∩ B₁` is the monotone limit of
the `C_c(B₁)` cutoffs `innerApprox W m` (`PalmInnerApprox`), so the nonnegative Palm identity (`lintegral_palm_test`,
`PalmLintegralPalm`) passes to `W ∩ B₁` by monotone convergence in `m`. The random measure enters through a measurable
kernel `κ` that agrees almost surely with `μ_ω` restricted to `B₁`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The mass of `W ∩ B₁` is the supremum of the integrals of the cutoffs `innerApprox W m`, for `W` open. -/
theorem measure_inter_ball_eq_iSup {κ : Measure ℂ} {W : Set ℂ} (hW : IsOpen W) :
    κ (W ∩ ball (0 : ℂ) 1) = ⨆ m : ℕ, ∫⁻ z, ENNReal.ofReal (innerApprox W m z) ∂κ := by
  have hm : MeasurableSet (W ∩ ball (0 : ℂ) 1) := hW.measurableSet.inter measurableSet_ball
  rw [← lintegral_indicator_one hm, lintegral_congr (fun z => innerApprox_iSup hW z)]
  exact lintegral_iSup (f := fun m z => ENNReal.ofReal (innerApprox W m z))
    (fun m => ENNReal.measurable_ofReal.comp (innerApprox_continuous W m).measurable)
    (fun m m' hmm z => ENNReal.ofReal_le_ofReal (innerApprox_mono W z hmm))

/-- Pulling a supremum over an increasing sequence out of a product with a fixed factor (monotone convergence). -/
theorem lintegral_mul_iSup_seq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f : Ω → ℝ≥0∞}
    {g : ℕ → Ω → ℝ≥0∞} (hf : Measurable f) (hg : ∀ m, Measurable (g m)) (hmono : Monotone g) :
    ∫⁻ ω, f ω * ⨆ m, g m ω ∂P = ⨆ m, ∫⁻ ω, f ω * g m ω ∂P := by
  simp_rw [ENNReal.mul_iSup]
  exact lintegral_iSup (f := fun m ω => f ω * g m ω) (fun m => hf.mul (hg m))
    (fun m m' hmm ω => mul_le_mul_of_nonneg_left (hmono hmm ω) zero_le)

/-- The lintegral of the shifted test functional is the `ofReal` of its Bochner expectation (nonnegative `ψ`). -/
theorem lintegral_shifted_eq_ofReal {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {k : ℕ} {φ : Fin k → ℂ → ℝ}
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ψ : (Fin k → ℝ) → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C) (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P =
      ENNReal.ofReal (∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P) := by
  have hXm : ∀ j, Measurable (fun ω => hC ω (φ j)) := fun j => hG.measurable_pairing (φ j) (hφ j)
  have hm : Measurable fun ω => ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) :=
    hψ.measurable.comp (Measurable.of_eval fun j => (hXm j).add_const _)
  have hi : Integrable (fun ω => ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) P :=
    (integrable_const C).mono' hm.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hψC _)
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ω => hψ0 _)]

/-- Measurability in the marked point of the shifted lintegral. -/
theorem measurable_lintegral_shifted {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {k : ℕ} {φ : Fin k → ℂ → ℝ}
    (hφ : ∀ j, IsTestFunction Set.univ (φ j)) {ψ : (Fin k → ℝ) → ℝ} (hψ : Continuous ψ)
    (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C) :
    Measurable fun z : ℂ =>
      ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P := by
  have hfun : (fun z : ℂ =>
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P) =
      fun z : ℂ => ENNReal.ofReal (∫ ω, ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P) :=
    funext fun z => lintegral_shifted_eq_ofReal hG γ hφ hψ hψ0 hψC z
  rw [hfun]
  exact ENNReal.measurable_ofReal.comp (measurable_shifted_expectation hG γ hφ hψ)

/-- A function `z ↦ ofReal (η z)` whose support lies in `tsupport η ⊆ B₁` is supported in `B₁`. -/
theorem support_ofReal_subset_ball {η : ℂ → ℝ} (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    Function.support (fun z => ENNReal.ofReal (η z)) ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  rw [Function.mem_support] at hz
  have hz' : η z ≠ 0 := fun h0 => hz (by simp [h0])
  exact htsupp (subset_closure (Function.mem_support (f := η) |>.2 hz'))

/-- The integral against `μ.restrict B₁` of a function supported in `B₁` is the integral against `μ`. -/
theorem lintegral_ofReal_restrict_ball_eq {μ : Measure ℂ} {η : ℂ → ℝ}
    (htsupp : tsupport η ⊆ ball (0 : ℂ) 1) :
    ∫⁻ z, ENNReal.ofReal (η z) ∂(μ.restrict (ball (0 : ℂ) 1)) = ∫⁻ z, ENNReal.ofReal (η z) ∂μ :=
  setLIntegral_eq_of_support_subset (support_ofReal_subset_ball htsupp)

/-- The cutoffs `innerApprox W m` increase to the indicator of `W ∩ B₁`, so multiplying by `I` and taking the
supremum gives the indicator of `W ∩ B₁` times `I`. -/
theorem iSup_innerApprox_mul {W : Set ℂ} (hW : IsOpen W) (I : ℂ → ℝ≥0∞) (z : ℂ) :
    ⨆ m : ℕ, ENNReal.ofReal (innerApprox W m z) * I z = (W ∩ ball (0 : ℂ) 1).indicator I z := by
  rw [← ENNReal.iSup_mul (fun m : ℕ => ENNReal.ofReal (innerApprox W m z)) (I z),
    ← innerApprox_iSup hW z]
  by_cases hz : z ∈ W ∩ ball (0 : ℂ) 1
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, Pi.one_apply, one_mul]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, zero_mul]

/-- **Palm identity for open sets** (lintegral form; `ψ ≥ 0` bounded continuous on `ℝ^k`, test functions `φ`).
For `W` open, the marked mass of `W ∩ B₁` against `ψ(hC φ)` equals the integral over `W ∩ B₁` of the shifted
expectations. The kernel `κ` is measurable and a.s. equal to `μ_ω` restricted to `B₁`. Stated with the staged
unnormalized DMS hypothesis `hU`, kept explicit. -/
theorem lintegral_palm_open {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {κ : Ω → Measure ℂ} (hκm : Measurable κ) (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1))
    {W : Set ℂ} (hW : IsOpen W) {k : ℕ} {φ : Fin k → ℂ → ℝ} (hφ : ∀ j, IsTestFunction Set.univ (φ j))
    {ψ : (Fin k → ℝ) → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C) :
    ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (W ∩ ball (0 : ℂ) 1) ∂P =
      ∫⁻ z in W ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) := by
  have hXm : ∀ j, Measurable (fun ω => hC ω (φ j)) := fun j => hG.measurable_pairing (φ j) (hφ j)
  have hψX : Measurable fun ω => ENNReal.ofReal (ψ (fun j => hC ω (φ j))) :=
    ENNReal.measurable_ofReal.comp (hψ.measurable.comp (Measurable.of_eval fun j => hXm j))
  have hBm : MeasurableSet (W ∩ ball (0 : ℂ) 1) := hW.measurableSet.inter measurableSet_ball
  -- the cutoffs and their integrals against `κ ω`
  have hfm : ∀ m : ℕ, Measurable fun z : ℂ => ENNReal.ofReal (innerApprox W m z) :=
    fun m => ENNReal.measurable_ofReal.comp (innerApprox_continuous W m).measurable
  have hAm : ∀ m : ℕ, Measurable fun ω => ∫⁻ z, ENNReal.ofReal (innerApprox W m z) ∂(κ ω) :=
    fun m => (Measure.measurable_lintegral (hfm m)).comp hκm
  have hAmono : Monotone (fun (m : ℕ) (ω : Ω) => ∫⁻ z, ENNReal.ofReal (innerApprox W m z) ∂(κ ω)) :=
    fun m m' hmm ω => lintegral_mono fun z => ENNReal.ofReal_le_ofReal (innerApprox_mono W z hmm)
  -- the shifted expectations, and the products with the cutoffs
  have hIm := measurable_lintegral_shifted hG γ hφ hψ hψ0 hψC
  have hF : ∀ m : ℕ, Measurable fun z : ℂ => ENNReal.ofReal (innerApprox W m z) *
      ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P :=
    fun m => (hfm m).mul hIm
  have hFmono : Monotone (fun (m : ℕ) (z : ℂ) => ENNReal.ofReal (innerApprox W m z) *
      ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P) :=
    fun m m' hmm z =>
      mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (innerApprox_mono W z hmm)) zero_le
  -- left side: the mass of `W ∩ B₁` is the supremum over the cutoffs, then monotone convergence in `ω`
  have hL1 : ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (W ∩ ball (0 : ℂ) 1) ∂P =
      ⨆ m : ℕ, ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) *
        ∫⁻ z, ENNReal.ofReal (innerApprox W m z) ∂(κ ω) ∂P := by
    simp only [measure_inter_ball_eq_iSup hW]
    exact lintegral_mul_iSup_seq hψX hAm hAmono
  -- each cutoff: the Palm identity, after replacing `κ ω` by `μ ω` (both restricted to `B₁`)
  have hL2 : ∀ m : ℕ, ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) *
        ∫⁻ z, ENNReal.ofReal (innerApprox W m z) ∂(κ ω) ∂P =
      ∫⁻ z, ENNReal.ofReal (innerApprox W m z) *
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) := by
    intro m
    have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) *
        ∫⁻ z, ENNReal.ofReal (innerApprox W m z) ∂(κ ω) =
        ENNReal.ofReal (ψ (fun j => hC ω (φ j))) *
          ∫⁻ z, ENNReal.ofReal (innerApprox W m z) ∂(μ ω) := by
      filter_upwards [hκa] with ω hω
      rw [hω, lintegral_ofReal_restrict_ball_eq (innerApprox_tsupport W m)]
    rw [lintegral_congr_ae hae]
    exact lintegral_palm_test hG γ hμ hU (innerApprox_continuous W m)
      (innerApprox_hasCompactSupport W m) (innerApprox_nonneg W m) (innerApprox_tsupport W m) hφ hψ hψ0 hψC
  -- right side: monotone convergence in `m` and then the indicator of `W ∩ B₁`
  rw [hL1]
  simp only [hL2]
  have hpt : ∀ z : ℂ,
      ⨆ m : ℕ, ENNReal.ofReal (innerApprox W m z) *
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P =
      (W ∩ ball (0 : ℂ) 1).indicator
        (fun z : ℂ => ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P) z :=
    fun z => iSup_innerApprox_mul hW
      (fun z : ℂ => ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P) z
  rw [← lintegral_iSup hF hFmono, lintegral_congr hpt]
  exact lintegral_indicator hBm _

end HarmonicBalls

end
