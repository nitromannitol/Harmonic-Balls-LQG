import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmBorelExtension

/-! # Route (A), Step M: the Palm identity for measurable functionals of the pairing (P3.5)

For a Borel set `B ⊆ ℂ`, both sides of the Borel identity (`lintegral_palm_borel`, `PalmBorelExtension`) are integrals
against finite measures on `Fin k → ℝ`: the image of `P.withDensity (κ · (B ∩ B₁))` under `ω ↦ (hC ω φ_j)_j`, and the image
of `(vol|_{B ∩ B₁}) ⊗ P` under `(z, ω) ↦ (hC ω φ_j + ∫ dmsShift_z φ_j)_j`. The Borel identity says that they agree on
nonnegative bounded continuous functions; uniqueness of finite Borel measures then gives agreement on every measurable
functional of the pairing. -/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The mass bound `∫⁻ κ_ω(B₁) dP < ∞` for `κ = μ|_{B₁}` almost surely (the Palm identity with `ψ ≡ 1`). -/
theorem lintegral_kernel_ball_lt_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {κ : Ω → Measure ℂ} (hκm : Measurable κ) (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1))
    {k : ℕ} {φ : Fin k → ℂ → ℝ} (hφ : ∀ j, IsTestFunction Set.univ (φ j)) :
    ∫⁻ ω, κ ω (Set.univ ∩ ball (0 : ℂ) 1) ∂P < ⊤ := by
  have h1 := lintegral_palm_open hG γ hμ hU hκm hκa isOpen_univ hφ
    (continuous_const : Continuous fun _ : Fin k → ℝ => (1 : ℝ)) (fun _ => zero_le_one) (C := 1)
    (fun _ => by simp)
  simp only [ENNReal.ofReal_one, one_mul, lintegral_const, measure_univ, mul_one,
    Measure.restrict_apply_univ] at h1
  rw [h1, Set.univ_inter]
  exact measure_ball_lt_top

/-- **Palm identity for measurable functionals** (ψ-extension of `lintegral_palm_borel`): for a measurable
`Ψ : (Fin k → ℝ) → ℝ≥0∞` and a Borel set `B`, the marked integral of `Ψ(hC φ)` against `κ_ω(B ∩ B₁)` equals the integral
over `B ∩ B₁` of the shifted expectations of `Ψ`. -/
theorem lintegral_palm_psi {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {κ : Ω → Measure ℂ} (hκm : Measurable κ) (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1))
    {k : ℕ} {φ : Fin k → ℂ → ℝ} (hφ : ∀ j, IsTestFunction Set.univ (φ j))
    {B : Set ℂ} (hB : MeasurableSet B) {Ψ : (Fin k → ℝ) → ℝ≥0∞} (hΨ : Measurable Ψ) :
    ∫⁻ ω, Ψ (fun j => hC ω (φ j)) * κ ω (B ∩ ball (0 : ℂ) 1) ∂P =
      ∫⁻ z in B ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, Ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P ∂(volume : Measure ℂ) := by
  have hX : Measurable fun ω => fun j => hC ω (φ j) :=
    Measurable.of_eval fun j => hG.measurable_pairing (φ j) (hφ j)
  have hF : Measurable fun p : ℂ × Ω => fun j => hC p.2 (φ j) + ∫ x, dmsShift γ p.1 x * φ j x :=
    Measurable.of_eval fun j => ((hG.measurable_pairing (φ j) (hφ j)).comp measurable_snd).add
      ((measurable_integral_dmsShift γ (hφ j).1.continuous).comp measurable_fst)
  have hdens : Measurable fun ω => κ ω (B ∩ ball (0 : ℂ) 1) :=
    (Measure.measurable_coe (hB.inter measurableSet_ball)).comp hκm
  -- the two finite measures on `Fin k → ℝ`
  obtain ⟨m₁, hm₁⟩ : ∃ m : Measure (Fin k → ℝ),
      m = (P.withDensity fun ω => κ ω (B ∩ ball (0 : ℂ) 1)).map fun ω j => hC ω (φ j) := ⟨_, rfl⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m : Measure (Fin k → ℝ),
      m = (((volume : Measure ℂ).restrict (B ∩ ball (0 : ℂ) 1)).prod P).map
        fun p : ℂ × Ω => fun j => hC p.2 (φ j) + ∫ x, dmsShift γ p.1 x * φ j x := ⟨_, rfl⟩
  -- the two marginal formulas, for every measurable functional
  have hL : ∀ Ψ' : (Fin k → ℝ) → ℝ≥0∞, Measurable Ψ' →
      ∫⁻ x, Ψ' x ∂m₁ = ∫⁻ ω, Ψ' (fun j => hC ω (φ j)) * κ ω (B ∩ ball (0 : ℂ) 1) ∂P := by
    intro Ψ' hΨ'
    have hΨ'X : Measurable fun ω => Ψ' (fun j => hC ω (φ j)) := hΨ'.comp hX
    rw [hm₁, lintegral_map hΨ' hX, lintegral_withDensity_eq_lintegral_mul _ hdens hΨ'X]
    exact lintegral_congr fun ω => mul_comm _ _
  have hR : ∀ Ψ' : (Fin k → ℝ) → ℝ≥0∞, Measurable Ψ' →
      ∫⁻ x, Ψ' x ∂m₂ = ∫⁻ z in B ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, Ψ' (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∂P ∂(volume : Measure ℂ) := by
    intro Ψ' hΨ'
    have hΨ'F : Measurable fun p : ℂ × Ω => Ψ' (fun j => hC p.2 (φ j) + ∫ x, dmsShift γ p.1 x * φ j x) :=
      hΨ'.comp hF
    rw [hm₂, lintegral_map hΨ' hF]
    exact lintegral_prod _ hΨ'F.aemeasurable
  -- `m₁` is finite (the Palm mass of `B₁`)
  have hfin₁ : IsFiniteMeasure m₁ := by
    have h1 := hL (fun _ => 1) measurable_const
    simp only [one_mul, lintegral_one] at h1
    refine ⟨?_⟩
    rw [h1]
    exact lt_of_le_of_lt
      (lintegral_mono fun ω => measure_mono (Set.inter_subset_inter (Set.subset_univ B) Set.Subset.rfl))
      (lintegral_kernel_ball_lt_top hG γ hμ hU hκm hκa hφ)
  -- on bounded continuous functions the two measures agree, by the Borel identity
  have hkey : ∀ (ψ : (Fin k → ℝ) → ℝ) (C : ℝ), Continuous ψ → (∀ x, 0 ≤ ψ x) → (∀ x, |ψ x| ≤ C) →
      ∫⁻ x, ENNReal.ofReal (ψ x) ∂m₁ = ∫⁻ x, ENNReal.ofReal (ψ x) ∂m₂ := by
    intro ψ C hψc hψ0 hψC
    have hΨ0 : Measurable fun x => ENNReal.ofReal (ψ x) :=
      ENNReal.measurable_ofReal.comp hψc.measurable
    rw [hL _ hΨ0, hR _ hΨ0]
    exact lintegral_palm_borel hG γ hμ hU hκm hκa hφ hψc hψ0 hψC hB
  -- uniqueness of finite Borel measures on `Fin k → ℝ`
  have hm : m₁ = m₂ := by
    refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f => ?_
    obtain ⟨C₀, hC₀⟩ := BoundedContinuousMapClass.map_bounded f
    have hbd : ∀ x, |(f x : ℝ)| ≤ (f 0 : ℝ) + C₀ := fun x => by
      have h := hC₀ x 0
      rw [NNReal.dist_eq] at h
      have h' := (abs_le.1 h).2
      rw [abs_of_nonneg (NNReal.coe_nonneg _)]
      linarith
    have hfc : Continuous fun x => (f x : ℝ) := NNReal.continuous_coe.comp f.continuous
    have h0 : ∀ x, 0 ≤ (f x : ℝ) := fun x => NNReal.coe_nonneg _
    have hfK := hkey (fun x => (f x : ℝ)) ((f 0 : ℝ) + C₀) hfc h0 hbd
    simpa only [ENNReal.ofReal_coe_nnreal] using hfK
  -- the Palm identity for `Ψ`
  rw [← hL Ψ hΨ, hm]
  exact hR Ψ hΨ

end HarmonicBalls

end
