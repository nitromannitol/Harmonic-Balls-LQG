import HarmonicBalls.Steps.Sec11.ScalingMomentComparison

/-! # Puncture criterion with deterministic scale constants

A uniform diameter moment normalized by arbitrary positive finite scale
constants implies the exponential-normalization criterion when their ratios
are uniformly bounded. The moment and ratio bounds remain explicit.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- Local internal diameter normalized by a deterministic scale constant
and a circle average. -/
noncomputable def scaledBallDiameterWithScale
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (s ξ ε : ℝ) (c : ℕ → ℂ) (a : ℕ → ℝ≥0∞) (n i : ℕ) (ω : Ω) : ℝ≥0∞ :=
  (⨆ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
    ⨆ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
      internalMetric (D ω)
        (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))) x y) /
    (a n * ENNReal.ofReal (Real.exp (ξ * hcirc ω (Real.exp (-(s + n))) 0)))

/-- Comparison of the moments with deterministic and exponential scale
normalizations. -/
theorem scaledBallNormalizedInternalDiameter_lintegral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (s ξ η ε : ℝ) (c : ℕ → ℂ) (a : ℕ → ℝ≥0∞) (n i : ℕ) (A C : ℝ≥0∞)
    (ha0 : a n ≠ 0) (hatop : a n ≠ ∞) (hAtop : A ≠ ∞)
    (hratio : a n / ENNReal.ofReal (Real.exp (-η * (n : ℝ))) ≤ A)
    (hmoment : (∫⁻ ω, scaledBallDiameterWithScale D hcirc s ξ ε c a n i ω ∂P) ≤ C) :
    (∫⁻ ω, scaledBallNormalizedInternalDiameter D hcirc s ξ η ε c n i ω ∂P) ≤ A * C := by
  let F (ω : Ω) := ⨆ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
    ⨆ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
      internalMetric (D ω)
        (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))) x y
  let B (ω : Ω) := ENNReal.ofReal (Real.exp (ξ * hcirc ω (Real.exp (-(s + n))) 0))
  have h := lintegral_normalized_diameter_le_of_scale_ratio P F B (a n)
    (ENNReal.ofReal (Real.exp (-η * (n : ℝ)))) A C ha0 hatop
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne' ENNReal.ofReal_ne_top hAtop hratio hmoment
  simpa only [scaledBallNormalizedInternalDiameter, F, B, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_nonneg _)] using h

/-- Finitely many center-dependent moment bounds have a common finite bound. -/
theorem exists_uniform_lintegral_bound_of_finite_centers
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → ℕ → Ω → ℝ≥0∞) (N : ℕ)
    (h : ∀ i, i ≤ N → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n, (∫⁻ ω, F n i ω ∂P) ≤ C) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n i, i ≤ N → (∫⁻ ω, F n i ω ∂P) ≤ C := by
  classical
  have hex (i : ℕ) : ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      (i ≤ N → ∀ n, (∫⁻ ω, F n i ω ∂P) ≤ C) := by
    by_cases hi : i ≤ N
    · obtain ⟨C, hC, hbound⟩ := h i hi
      exact ⟨C, hC, fun _ => hbound⟩
    · exact ⟨0, ENNReal.zero_ne_top, fun hi' => (hi hi').elim⟩
  choose C hC hbound using hex
  refine ⟨∑ i ∈ Finset.range (N + 1), C i, ?_, ?_⟩
  · exact ENNReal.sum_ne_top.mpr (fun i _ => hC i)
  · intro n i hi
    calc
      _ ≤ C i := hbound i hi n
      _ ≤ ∑ j ∈ Finset.range (N + 1), C j := by
        apply Finset.single_le_sum
        · intro j _
          exact bot_le
        · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hi)

/-- Uniform moments with deterministic scale constants and a uniform bound on
their ratios imply logarithmic Weyl puncture removal. -/
theorem exists_scaled_ball_criterion_of_scale_diameter_moments
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
      ∀ (a : ℕ → ℝ≥0∞) (A C : ℝ≥0∞),
        (∀ n, a n ≠ 0) → (∀ n, a n ≠ ∞) → A ≠ ∞ → C ≠ ∞ →
        (∀ n, a n / ENNReal.ofReal (Real.exp (-η * (n : ℝ))) ≤ A) →
        (∀ n i, i ≤ N → (∫⁻ ω, scaledBallDiameterWithScale D hcirc s ξ ε c a n i ω ∂P) ≤ C) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_explicit_diameter_moments P hC hcirc hh D E s ξ α β κ η
      hs hξ hα hgap hκ hη V hball hmeasD hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro a A C ha0 hatop hAtop hCtop hratio hmoment
  apply hcriterion (A * C) (ENNReal.mul_ne_top hAtop hCtop)
  intro n i hi
  exact scaledBallNormalizedInternalDiameter_lintegral_le P D hcirc s ξ η ε c a n i A C
    (ha0 n) (hatop n) hAtop (hratio n) (hmoment n i hi)

/-- Center-dependent moment bounds suffice for the finite ball cover. -/
theorem exists_scaled_ball_criterion_of_centerwise_diameter_moments
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
      ∀ (a : ℕ → ℝ≥0∞) (A : ℝ≥0∞),
        (∀ n, a n ≠ 0) → (∀ n, a n ≠ ∞) → A ≠ ∞ →
        (∀ n, a n / ENNReal.ofReal (Real.exp (-η * (n : ℝ))) ≤ A) →
        (∀ i, i ≤ N → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n,
          (∫⁻ ω, scaledBallDiameterWithScale D hcirc s ξ ε c a n i ω ∂P) ≤ C) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_scale_diameter_moments P hC hcirc hh D E s ξ α β κ η
      hs hξ hα hgap hκ hη V hball hmeasD hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro a A ha0 hatop hAtop hratio hmoment
  obtain ⟨C, hCfin, hbound⟩ := exists_uniform_lintegral_bound_of_finite_centers P
    (scaledBallDiameterWithScale D hcirc s ξ ε c a) N hmoment
  exact hcriterion a A C ha0 hatop hAtop hCfin hratio hbound

#print axioms scaledBallNormalizedInternalDiameter_lintegral_le
#print axioms exists_uniform_lintegral_bound_of_finite_centers
#print axioms exists_scaled_ball_criterion_of_scale_diameter_moments
#print axioms exists_scaled_ball_criterion_of_centerwise_diameter_moments

end HarmonicBalls
