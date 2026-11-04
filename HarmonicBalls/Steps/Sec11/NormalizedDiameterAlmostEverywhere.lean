import HarmonicBalls.Steps.Sec11.NormalizedDiameterMoment
import HarmonicBalls.Steps.Sec11.InternalMetricMeasurable
import HarmonicBalls.Steps.Sec11.CountableClearanceChains

/-! # Almost-everywhere normalized diameter bounds

An almost-everywhere distance bound can be made pointwise by assigning an
infinite normalizing variable on the exceptional set. This does not change
its almost-everywhere measurability or its integral.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- The internal-distance supremum over two fixed subsets is almost-everywhere
measurable for a pointwise measurable random Euclidean length metric. -/
theorem aemeasurable_iSup_internalMetric_of_ae_lengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    {V A B : Set ℂ} (hV : IsOpen V) (hA : A ⊆ V) (hB : B ⊆ V)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    AEMeasurable (fun ω => ⨆ x ∈ A, ⨆ y ∈ B, internalMetric (D ω) V x y) P := by
  obtain ⟨D', hD', hmetric', hEq⟩ := exists_measurable_lengthMetric_modification hD hmetric
  have hnonneg (ω : Ω) (x y : ℂ) : 0 ≤ D' ω x y := by
    have h := (hmetric' ω).triangle x y x
    rw [(hmetric' ω).self_eq_zero, (hmetric' ω).symm y x] at h
    linarith
  have hm := measurable_iSup_internalMetric hV hA hB hmetric' hnonneg
    (fun x hx y _ => measurable_internalMetric_of_lengthMetric hV (hA hx) y hD' hmetric')
  apply hm.aemeasurable.congr
  filter_upwards [hEq] with ω hω
  rw [hω]

/-- The normalized internal diameter is almost-everywhere measurable and
bounds each internal distance after restoring the normalizing factor. -/
theorem normalized_internalDiameter_measurable_and_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    {V A : Set ℂ} (hV : IsOpen V) (hA : A ⊆ V)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (B : Ω → ℝ≥0∞) (hB : AEMeasurable B P)
    (hB0 : ∀ ω, B ω ≠ 0) (hBtop : ∀ ω, B ω ≠ ∞) :
    AEMeasurable (fun ω => (⨆ x ∈ A, ⨆ y ∈ A,
      internalMetric (D ω) V x y) / B ω) P ∧
    ∀ ω, ∀ x ∈ A, ∀ y ∈ A, internalMetric (D ω) V x y ≤
      B ω * ((⨆ x ∈ A, ⨆ y ∈ A, internalMetric (D ω) V x y) / B ω) := by
  constructor
  · exact (aemeasurable_iSup_internalMetric_of_ae_lengthMetric hV hA hA hD hmetric).div hB
  · intro ω x hx y hy
    rw [mul_comm, ENNReal.div_mul_cancel (hB0 ω) (hBtop ω)]
    exact le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

/-- An almost-everywhere bound by a positive multiple has a pointwise
representative with the same almost-everywhere values. -/
theorem exists_pointwise_diameter_envelope
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (K W : Set ℂ)
    (B X : Ω → ℝ≥0∞) (hB : ∀ ω, B ω ≠ 0)
    (hbound : ∀ᵐ ω ∂P, ∀ x ∈ K, ∀ y ∈ K,
      internalMetric (D ω) W x y ≤ B ω * X ω) :
    ∃ Y : Ω → ℝ≥0∞, Y =ᵐ[P] X ∧
      ∀ ω, ∀ x ∈ K, ∀ y ∈ K, internalMetric (D ω) W x y ≤ B ω * Y ω := by
  classical
  let G (ω : Ω) : Prop := ∀ x ∈ K, ∀ y ∈ K,
    internalMetric (D ω) W x y ≤ B ω * X ω
  let Y (ω : Ω) : ℝ≥0∞ := if G ω then X ω else ∞
  refine ⟨Y, ?_, ?_⟩
  · filter_upwards [hbound] with ω hω
    simp only [Y, show G ω from hω, ↓reduceIte]
  · intro ω x hx y hy
    by_cases h : G ω
    · simpa [Y, h] using h x hx y hy
    · simp only [Y, h, ↓reduceIte, ENNReal.mul_top (hB ω), le_top]

/-- Almost-everywhere normalized local diameter bounds and uniform first
moments yield logarithmic Weyl puncture removal. -/
theorem exists_scaled_ball_criterion_of_ae_normalized_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (s ξ α β κ η : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α)
    (hgap : ξ * α < β) (hκ : β < κ) (hη : κ < η)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ∀ (X : ℕ → ℕ → Ω → ℝ≥0∞) (C : ℝ≥0∞), C ≠ ∞ →
        (∀ (n i : ℕ), i ≤ N → AEMeasurable (X n i) P) →
        (∀ (n i : ℕ), i ≤ N → (∫⁻ ω, X n i ω ∂P) ≤ C) →
        (∀ (n i : ℕ), i ≤ N → ∀ᵐ ω ∂P,
          ∀ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
          ∀ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
            internalMetric (D ω)
              (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))) x y ≤
              ENNReal.ofReal (Real.exp (-η * (n : ℝ) +
                ξ * hcirc ω (Real.exp (-(s + n))) 0)) * X n i ω) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_normalized_moments P hC hcirc hh D E s ξ α β κ η
      hs hξ hα hgap hκ hη V hball hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro X C hCfin hmeas hmoment hbound
  classical
  let K (n i : ℕ) := ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε)
  let W (n i : ℕ) := ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))
  let B (n : ℕ) (ω : Ω) := ENNReal.ofReal (Real.exp (-η * (n : ℝ) +
    ξ * hcirc ω (Real.exp (-(s + n))) 0))
  have hexists (n i : ℕ) : ∃ Y : Ω → ℝ≥0∞, Y =ᵐ[P] X n i ∧
      (i ≤ N → ∀ ω, ∀ x ∈ K n i, ∀ y ∈ K n i,
        internalMetric (D ω) (W n i) x y ≤ B n ω * Y ω) := by
    by_cases hi : i ≤ N
    · obtain ⟨Y, heq, hY⟩ := exists_pointwise_diameter_envelope P D (K n i) (W n i)
        (B n) (X n i) (fun ω => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
        (hbound n i hi)
      exact ⟨Y, heq, fun _ => hY⟩
    · exact ⟨X n i, Filter.EventuallyEq.rfl, fun h => (hi h).elim⟩
  choose Y heq hpoint using hexists
  apply hcriterion Y C hCfin
  · intro n i hi
    exact (hmeas n i hi).congr (heq n i).symm
  · intro n i hi
    rw [lintegral_congr_ae (heq n i)]
    exact hmoment n i hi
  · intro n i hi
    exact hpoint n i hi

#print axioms aemeasurable_iSup_internalMetric_of_ae_lengthMetric
#print axioms normalized_internalDiameter_measurable_and_bound
#print axioms exists_pointwise_diameter_envelope
#print axioms exists_scaled_ball_criterion_of_ae_normalized_moments

end HarmonicBalls
