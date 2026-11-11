import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Lemma 11.7: applying the frozen local Campbell input to a measurable bad set (sections 6-7)

Given a measurable set `S` of marked observations `(z, o)` (`z ∈ ℂ`, `o` a mean-zero observation of `h^ℂ` on the disk `D`),
suppose that the reference bad section has zero `z`-integral over `U` (Lebesgue measure). Then the frozen input
`LocalCampbellMarkedRestrictionFrozen` (Frozen/S11c.lean) gives a zero lintegral of the `μ_ω`-weighted marked integrand;
since that integrand is a.s.-measurable, it vanishes almost surely, and hence for almost every field, `μ_ω`-almost every
`z ∈ U` has its marked observation outside `S`.

The only external input is the frozen Campbell statement. The a.s.-measurability of the weighted integrand is a hypothesis
here (`hF`), to be discharged in the final assembly from the measurable profile framework (`LQGMeasureOfProfileMeasurableFrozen`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls.S11c

universe u

/-- From the zero reference lintegral over `U` and the frozen local Campbell input,
almost every field has `μ_ω`-almost no `z ∈ U` with marked observation in `S`. -/
theorem campbell_marked_ae_notMem
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCamp : LocalCampbellMarkedRestrictionFrozen.{u})
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (href : (∫⁻ z in ball c₁ r₁, (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P)) = 0)
    (hF : AEMeasurable (fun ω => (μ ω (ball c₁ r₁))⁻¹ * ∫⁻ z in ball c₁ r₁,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω)) P) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball c₁ r₁ →
      campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z ∉ S := by
  have hint := hCamp γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hh hμ c₁ c₂ r₁ r₂ hr₁ hr₂ hsub h0 S hS href
  have hzero := (lintegral_eq_zero_iff' hF).1 hint
  have hfin : ∀ᵐ ω ∂P, μ ω (ball c₁ r₁) < ∞ := by
    filter_upwards [hμ] with ω hω
    have := hω.isLocallyFiniteMeasure
    exact measure_ball_lt_top
  filter_upwards [hzero, hfin] with ω hω hfω
  -- the weighted integral over `U` vanishes for this `ω`
  have hI : ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
    by_cases h : μ ω (ball c₁ r₁) = 0
    · rw [Measure.restrict_eq_zero.2 h]
      simp
    · have hne : (μ ω (ball c₁ r₁))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfω.ne
      exact (mul_eq_zero.1 hω).resolve_left hne
  -- measurability of `z ↦ 1_S (z, c)` (the second marked coordinate does not depend on `z`)
  have hmap : Measurable fun z : ℂ => campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z :=
    measurable_id.prodMk measurable_const
  have hmeasZ : Measurable fun z : ℂ =>
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) :=
    (measurable_const.indicator hS).comp hmap
  have hae : ∀ᵐ z ∂((μ ω).restrict (ball c₁ r₁)),
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) = 0 :=
    (lintegral_eq_zero_iff hmeasZ).1 hI
  have hae' : ∀ᵐ z ∂(μ ω), z ∈ ball c₁ r₁ →
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) = 0 :=
    (ae_restrict_iff' measurableSet_ball).1 hae
  filter_upwards [hae'] with z hz hzU hmem
  have h1 := hz hzU
  rw [Set.indicator_of_mem hmem] at h1
  exact one_ne_zero h1

end HarmonicBalls.S11c
