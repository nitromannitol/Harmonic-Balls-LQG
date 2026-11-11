import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmZExtension

/-! # Route (A), Step M: the Palm identity for Borel sets of marked points (P3.4)

For a fixed nonnegative bounded continuous `ψ` on `ℝ^k`, both sides of the open-set identity (`lintegral_palm_open`,
`PalmZExtension`) are the values on `B ∩ B₁` of finite measures on `ℂ`: the marked measure
`B ↦ ∫⁻ ψ(hC φ) κ_ω(B ∩ B₁) dP` and the shifted measure `B ↦ ∫⁻_{B ∩ B₁} E[ψ(hC φ + ∫ dmsShift_z φ)] dz`.
They agree on open sets and on the whole plane. Open sets form a π-system generating the Borel σ-algebra, so the two
measures agree on all Borel sets.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The marked measure `B ↦ ∫⁻ ω, f ω * κ ω (B ∩ B₁) ∂P` on `ℂ`: the bind of `P.withDensity f` along
`ω ↦ (κ ω)|_{B₁}`. -/
def palmMarkedMass {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : Ω → Measure ℂ) (f : Ω → ℝ≥0∞) :
    Measure ℂ :=
  (P.withDensity f).bind fun ω => (κ ω).restrict (ball (0 : ℂ) 1)

/-- The shifted measure `B ↦ ∫⁻ z in B ∩ B₁, I z` on `ℂ`. -/
def palmShiftedMass (I : ℂ → ℝ≥0∞) : Measure ℂ :=
  (volume : Measure ℂ).withDensity ((ball (0 : ℂ) 1).indicator I)

/-- The restriction of a measurable kernel to `B₁` is a measurable map to measures. -/
theorem measurable_restrict_ball_kernel {Ω : Type*} [MeasurableSpace Ω] {κ : Ω → Measure ℂ}
    (hκm : Measurable κ) : Measurable fun ω => (κ ω).restrict (ball (0 : ℂ) 1) := by
  refine Measure.measurable_of_measurable_coe _ fun t ht => ?_
  simp only [Measure.restrict_apply ht]
  exact (Measure.measurable_coe (ht.inter measurableSet_ball)).comp hκm

/-- The value of the marked measure on a Borel set. -/
theorem palmMarkedMass_apply {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {κ : Ω → Measure ℂ}
    (hκm : Measurable κ) {f : Ω → ℝ≥0∞} (hf : Measurable f) {B : Set ℂ} (hB : MeasurableSet B) :
    palmMarkedMass P κ f B = ∫⁻ ω, f ω * κ ω (B ∩ ball (0 : ℂ) 1) ∂P := by
  unfold palmMarkedMass
  have hK := measurable_restrict_ball_kernel hκm
  have hg : Measurable fun ω => (κ ω).restrict (ball (0 : ℂ) 1) B :=
    (Measure.measurable_coe hB).comp hK
  rw [Measure.bind_apply hB hK.aemeasurable]
  rw [lintegral_withDensity_eq_lintegral_mul _ hf hg]
  refine lintegral_congr fun ω => ?_
  simp only [Pi.mul_apply, Measure.restrict_apply hB]

/-- The value of the shifted measure on a Borel set. -/
theorem palmShiftedMass_apply {I : ℂ → ℝ≥0∞} {B : Set ℂ} (hB : MeasurableSet B) :
    palmShiftedMass I B = ∫⁻ z in B ∩ ball (0 : ℂ) 1, I z ∂(volume : Measure ℂ) := by
  unfold palmShiftedMass
  rw [withDensity_apply _ hB, ← lintegral_indicator hB ((ball (0 : ℂ) 1).indicator I),
    Set.indicator_indicator, lintegral_indicator (hB.inter measurableSet_ball)]

/-- Two finite measures on `ℂ` that agree on open sets and on the whole plane agree on Borel sets (π-λ). -/
theorem measure_eq_of_isOpen_of_univ {ν₁ ν₂ : Measure ℂ} [IsFiniteMeasure ν₁]
    (hopen : ∀ s : Set ℂ, IsOpen s → ν₁ s = ν₂ s) (huniv : ν₁ Set.univ = ν₂ Set.univ) : ν₁ = ν₂ :=
  ext_of_generate_finite {s : Set ℂ | IsOpen s} (BorelSpace.measurable_eq.trans rfl)
    (fun s (hs : IsOpen s) t (ht : IsOpen t) _ => hs.inter ht) (fun s hs => hopen s hs) huniv

/-- **Palm identity for Borel sets** (lintegral form; `ψ ≥ 0` bounded continuous on `ℝ^k`, test functions `φ`).
For `B` Borel, the marked mass of `B ∩ B₁` against `ψ(hC φ)` equals the integral over `B ∩ B₁` of the shifted
expectations. The kernel `κ` is measurable and a.s. equal to `μ_ω` restricted to `B₁`; the unnormalized DMS
hypothesis `hU` stays explicit. -/
theorem lintegral_palm_borel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {κ : Ω → Measure ℂ} (hκm : Measurable κ) (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1))
    {k : ℕ} {φ : Fin k → ℂ → ℝ} (hφ : ∀ j, IsTestFunction Set.univ (φ j))
    {ψ : (Fin k → ℝ) → ℝ} (hψ : Continuous ψ) (hψ0 : ∀ x, 0 ≤ ψ x) {C : ℝ} (hψC : ∀ x, |ψ x| ≤ C)
    {B : Set ℂ} (hB : MeasurableSet B) :
    ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (B ∩ ball (0 : ℂ) 1) ∂P =
      ∫⁻ z in B ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) := by
  have hfX : Measurable fun ω => ENNReal.ofReal (ψ (fun j => hC ω (φ j))) :=
    ENNReal.measurable_ofReal.comp
      (hψ.measurable.comp (Measurable.of_eval fun j => hG.measurable_pairing (φ j) (hφ j)))
  -- the total mass of `κ_ω(B₁)` is finite: the open-set identity with `ψ ≡ 1` and `W = ℂ`
  have hmass : ∫⁻ ω, κ ω (Set.univ ∩ ball (0 : ℂ) 1) ∂P < ⊤ := by
    have h1 := lintegral_palm_open hG γ hμ hU hκm hκa isOpen_univ hφ
      (continuous_const : Continuous fun _ : Fin k → ℝ => (1 : ℝ)) (fun _ => zero_le_one) (C := 1)
      (fun _ => by simp)
    simp only [ENNReal.ofReal_one, one_mul, lintegral_const, measure_univ, mul_one,
      Measure.restrict_apply_univ] at h1
    rw [h1, Set.univ_inter]
    exact measure_ball_lt_top
  have hfin : IsFiniteMeasure (palmMarkedMass P κ fun ω => ENNReal.ofReal (ψ (fun j => hC ω (φ j)))) := by
    refine ⟨?_⟩
    rw [palmMarkedMass_apply P hκm hfX MeasurableSet.univ]
    have hle : ∀ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (Set.univ ∩ ball (0 : ℂ) 1) ≤
        ENNReal.ofReal C * κ ω (Set.univ ∩ ball (0 : ℂ) 1) := fun ω =>
      mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hψC _))) zero_le
    calc ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (Set.univ ∩ ball (0 : ℂ) 1) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal C * κ ω (Set.univ ∩ ball (0 : ℂ) 1) ∂P := lintegral_mono hle
      _ = ENNReal.ofReal C * ∫⁻ ω, κ ω (Set.univ ∩ ball (0 : ℂ) 1) ∂P :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmass
  -- the two measures agree on open sets (open-set identity) and on the whole plane
  have hmeas : palmMarkedMass P κ (fun ω => ENNReal.ofReal (ψ (fun j => hC ω (φ j)))) =
      palmShiftedMass (fun z => ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P) := by
    refine measure_eq_of_isOpen_of_univ ?_ ?_
    · intro s hs
      rw [palmMarkedMass_apply P hκm hfX hs.measurableSet, palmShiftedMass_apply hs.measurableSet]
      exact lintegral_palm_open hG γ hμ hU hκm hκa hs hφ hψ hψ0 hψC
    · rw [palmMarkedMass_apply P hκm hfX MeasurableSet.univ, palmShiftedMass_apply MeasurableSet.univ]
      exact lintegral_palm_open hG γ hμ hU hκm hκa isOpen_univ hφ hψ hψ0 hψC
  calc ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j))) * κ ω (B ∩ ball (0 : ℂ) 1) ∂P
      = palmMarkedMass P κ (fun ω => ENNReal.ofReal (ψ (fun j => hC ω (φ j)))) B :=
        (palmMarkedMass_apply P hκm hfX hB).symm
    _ = palmShiftedMass
          (fun z => ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P) B := by
        rw [hmeas]
    _ = ∫⁻ z in B ∩ ball (0 : ℂ) 1,
        ∫⁻ ω, ENNReal.ofReal (ψ (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x)) ∂P
        ∂(volume : Measure ℂ) :=
        palmShiftedMass_apply hB

end HarmonicBalls

end
