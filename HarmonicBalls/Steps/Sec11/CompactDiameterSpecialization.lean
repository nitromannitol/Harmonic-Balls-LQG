import HarmonicBalls.Steps.Sec11.ScaleNormalizedDiameterCriterion
import HarmonicBalls.Steps.Sec11.AnnulusGreenDilation

/-! # Compact-set specialization for normalized diameters

The local ball diameter is bounded by the normalized internal diameter of
its closed ball. The latter is expressed in terms of one fixed compact set
and one fixed open set under positive dilation.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- Positive dilation sends a closed ball to its dilated closed ball. -/
theorem image_real_smul_closedBall {k : ℝ} (hk : 0 < k) (z : ℂ) (b : ℝ) :
    (fun x : ℂ => k • x) '' closedBall z b = closedBall (k • z) (k * b) := by
  have hmem (x : ℂ) : k • x ∈ closedBall (k • z) (k * b) ↔ x ∈ closedBall z b := by
    simp only [mem_closedBall, dist_smul₀, Real.norm_eq_abs, abs_of_pos hk,
      mul_le_mul_iff_right₀ hk]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hmem x).2 hx
  · intro hy
    refine ⟨k⁻¹ • y, (hmem _).1 ?_, ?_⟩
    · simpa only [smul_smul, mul_inv_cancel₀ hk.ne', one_smul] using hy
    · simp [hk.ne']

/-- A closed ball of positive radius is a compact connected set contained in
the concentric open ball of twice its radius. -/
theorem closedBall_compact_connected_subset_double (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (closedBall z ε) ∧ IsConnected (closedBall z ε) ∧
      closedBall z ε ⊆ ball z (2 * ε) ∧
      ∃ x ∈ closedBall z ε, ∃ y ∈ closedBall z ε, x ≠ y := by
  refine ⟨isCompact_closedBall z ε, Metric.isConnected_closedBall hε.le, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  · refine ⟨z, mem_closedBall_self hε.le, z + ((ε / 2 : ℝ) : ℂ), ?_, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (half_pos hε)]
      linarith
    · intro h
      have hz := congrArg (fun w : ℂ => w - z) h
      simp only [sub_self, add_sub_cancel_left] at hz
      have hz' : (ε / 2 : ℝ) = 0 := by exact_mod_cast hz.symm
      linarith

/-- The internal diameter of a dilated fixed compact set, normalized by a
positive scale constant and the circle average at the origin. -/
noncomputable def scaledCompactInternalDiameter
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (ξ : ℝ) (K U : Set ℂ) (r : ℝ) (a : ℝ≥0∞) (ω : Ω) : ℝ≥0∞ :=
  (⨆ x ∈ (fun z : ℂ => r • z) '' K,
    ⨆ y ∈ (fun z : ℂ => r • z) '' K,
      internalMetric (D ω) ((fun z : ℂ => r • z) '' U) x y) /
    (a * ENNReal.ofReal (Real.exp (ξ * hcirc ω r 0)))

/-- The normalized open-ball diameter is at most the normalized diameter of
the dilated closed ball in the dilated doubled open ball. -/
theorem scaledBallDiameterWithScale_le_compact
    {Ω : Type*} (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (s ξ ε : ℝ) (c : ℕ → ℂ) (a : ℕ → ℝ≥0∞) (n i : ℕ) (ω : Ω) :
    scaledBallDiameterWithScale D hcirc s ξ ε c a n i ω ≤
      scaledCompactInternalDiameter D hcirc ξ (closedBall (c i) ε)
        (ball (c i) (2 * ε)) (Real.exp (-(s + n))) (a n) ω := by
  simp only [scaledBallDiameterWithScale, scaledCompactInternalDiameter,
    image_real_smul_closedBall (Real.exp_pos _), image_real_smul_ball (Real.exp_pos _)]
  apply ENNReal.div_le_div_right
  apply iSup_le
  intro x
  apply iSup_le
  intro hx
  apply iSup_le
  intro y
  apply iSup_le
  intro hy
  exact le_iSup_of_le x (le_iSup_of_le (ball_subset_closedBall hx)
    (le_iSup_of_le y (le_iSup_of_le (ball_subset_closedBall hy) le_rfl)))

/-- A moment bound for the compact-set normalized diameter gives the needed
moment bound for the local ball. -/
theorem scaledBallDiameterWithScale_lintegral_le_compact
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (s ξ ε : ℝ) (c : ℕ → ℂ) (a : ℕ → ℝ≥0∞) (n i : ℕ) :
    (∫⁻ ω, scaledBallDiameterWithScale D hcirc s ξ ε c a n i ω ∂P) ≤
      ∫⁻ ω, scaledCompactInternalDiameter D hcirc ξ (closedBall (c i) ε)
        (ball (c i) (2 * ε)) (Real.exp (-(s + n))) (a n) ω ∂P :=
  lintegral_mono (scaledBallDiameterWithScale_le_compact D hcirc s ξ ε c a n i)

/-- Moment bounds for the dilated fixed compact balls imply logarithmic
Weyl puncture removal. -/
theorem exists_scaled_ball_criterion_of_compact_diameter_moments
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
        (∀ i, i ≤ N → ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ (n : ℕ),
          (∫⁻ ω, scaledCompactInternalDiameter D hcirc ξ (closedBall (c i) ε)
            (ball (c i) (2 * ε)) (Real.exp (-(s + n))) (a n) ω ∂P) ≤ C) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_centerwise_diameter_moments P hC hcirc hh D E s ξ α β κ η
      hs hξ hα hgap hκ hη V hball hmeasD hD hE hDnonneg hEnonneg hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro a A ha0 hatop hAtop hratio hmoment
  apply hcriterion a A ha0 hatop hAtop hratio
  intro i hi
  obtain ⟨C, hCfin, hbound⟩ := hmoment i hi
  refine ⟨C, hCfin, ?_⟩
  intro n
  exact (scaledBallDiameterWithScale_lintegral_le_compact P D hcirc s ξ ε c a n i).trans (hbound n)

#print axioms image_real_smul_closedBall
#print axioms closedBall_compact_connected_subset_double
#print axioms scaledBallDiameterWithScale_le_compact
#print axioms scaledBallDiameterWithScale_lintegral_le_compact
#print axioms exists_scaled_ball_criterion_of_compact_diameter_moments

end HarmonicBalls
