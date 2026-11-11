import HarmonicBalls.Steps.Sec11.NormalizedDiameterAlmostEverywhere

/-! # Explicit normalized local internal diameters

The normalizing variable in the puncture criterion can be chosen to be the
local internal diameter divided by its circle-average scale factor. The
uniform moment estimate remains an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- Local internal diameter divided by the exponential circle-average scale. -/
noncomputable def scaledBallNormalizedInternalDiameter
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (s ξ η ε : ℝ) (c : ℕ → ℂ) (n i : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (⨆ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
    ⨆ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
      internalMetric (D ω)
        (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))) x y) /
    ENNReal.ofReal (Real.exp (-η * (n : ℝ) + ξ * hcirc ω (Real.exp (-(s + n))) 0))

/-- A uniform first moment for the explicit normalized diameters implies
logarithmic Weyl puncture removal. -/
theorem exists_scaled_ball_criterion_of_explicit_diameter_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (s ξ α β κ η : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α)
    (hgap : ξ * α < β) (hκ : β < κ) (hη : κ < η)
    (V : Set ℂ) (hball : ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hmeasD : ∀ x y, Measurable fun ω => D ω x y)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y) :
    ∃ (ε : ℝ) (N : ℕ) (c : ℕ → ℂ), 0 < ε ∧
      ∀ C : ℝ≥0∞, C ≠ ∞ →
        (∀ n i, i ≤ N → (∫⁻ ω, scaledBallNormalizedInternalDiameter
          D hcirc s ξ η ε c n i ω ∂P) ≤ C) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_ae_normalized_moments P hC hcirc hh D E s ξ α β κ η
      hs hξ hα hgap hκ hη V hball hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro C hCfin hmoment
  let X := scaledBallNormalizedInternalDiameter D hcirc s ξ η ε c
  have hnorm (n i : ℕ) : AEMeasurable (X n i) P ∧ ∀ ω,
      ∀ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
      ∀ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
        internalMetric (D ω)
          (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))) x y ≤
          ENNReal.ofReal (Real.exp (-η * (n : ℝ) +
            ξ * hcirc ω (Real.exp (-(s + n))) 0)) * X n i ω := by
    have hsub : ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε) ⊆
        ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε)) := by
      apply ball_subset_ball
      have hr := Real.exp_pos (-(s + n))
      nlinarith
    have hB : Measurable (fun ω => ENNReal.ofReal (Real.exp (-η * (n : ℝ) +
        ξ * hcirc ω (Real.exp (-(s + n))) 0))) := by
      exact (measurable_const.add (measurable_const.mul
        (hh.measurable_circle _ _ (Real.exp_pos _)))).exp.ennreal_ofReal
    exact normalized_internalDiameter_measurable_and_bound isOpen_ball hsub hmeasD hD _
      hB.aemeasurable (fun _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (fun _ => ENNReal.ofReal_ne_top)
  apply hcriterion X C hCfin
  · intro n i _
    exact (hnorm n i).1
  · exact hmoment
  · intro n i _
    exact Filter.Eventually.of_forall (hnorm n i).2


end HarmonicBalls
