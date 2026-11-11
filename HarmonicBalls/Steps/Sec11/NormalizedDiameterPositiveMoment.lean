import HarmonicBalls.Steps.Sec11.NormalizedDiameterMoment
import HarmonicBalls.Steps.Sec11.ExplicitNormalizedDiameter

/-! # Positive moments and internal-diameter tails

Any positive moment of the normalized internal diameter gives the geometric
tail needed for puncture removal. The GFF formalization used here includes work
by Leonardo Bonanno on LatticeProb. -/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- A positive moment bounds exponential upper tails at a geometric rate. -/
theorem measure_exp_threshold_le_of_lintegral_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → ℝ≥0∞)
    (C : ℝ≥0∞) (a p : ℝ) (hp : 0 < p) (n : ℕ) (hX : AEMeasurable X P)
    (hC : (∫⁻ ω, (X ω) ^ p ∂P) ≤ C) :
    P {ω | ENNReal.ofReal (Real.exp (a * n)) ≤ X ω} ≤
      C * ENNReal.ofReal (Real.exp (-(a * p))) ^ n := by
  have hthreshold : ENNReal.ofReal (Real.exp (a * n)) ^ p =
      ENNReal.ofReal (Real.exp ((a * p) * n)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_nonneg _) hp.le,
      Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
    congr 2
    ring
  calc
    _ ≤ P {ω | ENNReal.ofReal (Real.exp ((a * p) * n)) ≤ (X ω) ^ p} := by
      apply measure_mono
      intro ω hω
      rw [← hthreshold]
      exact ENNReal.rpow_le_rpow hω hp.le
    _ ≤ _ := measure_exp_threshold_le_of_lintegral_le P (fun ω => (X ω) ^ p) C
      (a * p) n (ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hX) hC

open Filter in
/-- Uniform positive moments of normalized local distances give puncture
removal, with no first-moment assumption. -/
theorem exists_scaled_ball_criterion_of_normalized_positive_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (s ξ α β κ η p : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α)
    (hgap : ξ * α < β) (hκ : β < κ) (hη : κ < η) (hp : 0 < p)
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
        (∀ (n i : ℕ), i ≤ N → (∫⁻ ω, (X n i ω) ^ p ∂P) ≤ C) →
        (∀ (n i : ℕ), i ≤ N → ∀ ω,
          ∀ x ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
          ∀ y ∈ ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * ε),
            internalMetric (D ω)
              (ball (Real.exp (-(s + n)) • c i) (Real.exp (-(s + n)) * (2 * ε))) x y ≤
              ENNReal.ofReal (Real.exp (-η * (n : ℝ) +
                ξ * hcirc ω (Real.exp (-(s + n))) 0)) * X n i ω) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_circleAverage_tail P hC hcirc hh D E (fun _ => 1)
      s ξ α β κ hs hξ hα hgap hκ V hball hD hE hDnonneg hEnonneg
      (Filter.Eventually.of_forall (fun _ => ENNReal.one_ne_top)) hzero hscale
  refine ⟨ε, N, c, hε, ?_⟩
  intro X C hCfin hmeas hmoment hbound
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-((η - κ) * p)))
  have hq : q < 1 := by
    apply ENNReal.ofReal_lt_one.mpr
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (mul_pos (sub_pos.mpr hη) hp)
  have hsum : (∑' n : ℕ, C * q ^ n) ≠ ∞ := by
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    exact ENNReal.mul_ne_top hCfin (ENNReal.inv_ne_top.2 (tsub_pos_of_lt hq).ne')
  apply hcriterion (fun n => C * q ^ n) hsum
  intro n i hi
  calc
    _ ≤ P {ω | ENNReal.ofReal (Real.exp ((η - κ) * (n : ℝ))) ≤ X n i ω} := by
      apply measure_mono
      simpa only [one_mul] using internalMetric_exceedance_subset_exp_threshold D
        (fun ω => ξ * hcirc ω (Real.exp (-(s + n))) 0) (X n i) _ _ η κ n (hbound n i hi)
    _ ≤ C * q ^ n := measure_exp_threshold_le_of_lintegral_rpow_le P (X n i) C
      (η - κ) p hp n (hmeas n i hi) (hmoment n i hi)

/-- Positive moments of the explicit normalized local diameters imply
logarithmic Weyl puncture removal. -/
theorem exists_scaled_ball_criterion_of_explicit_positive_moments
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (D E : Ω → ℂ → ℂ → ℝ) (s ξ α β κ η p : ℝ)
    (hs : 0 ≤ s) (hξ : 0 < ξ) (hα : 0 ≤ α)
    (hgap : ξ * α < β) (hκ : β < κ) (hη : κ < η) (hp : 0 < p)
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
        (∀ n i, i ≤ N → (∫⁻ ω, (scaledBallNormalizedInternalDiameter
          D hcirc s ξ η ε c n i ω) ^ p ∂P) ≤ C) →
        ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
          internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  obtain ⟨ε, N, c, hε, hcriterion⟩ :=
    exists_scaled_ball_criterion_of_normalized_positive_moments P hC hcirc hh D E
      s ξ α β κ η p hs hξ hα hgap hκ hη hp V hball hD hE hDnonneg hEnonneg hzero hscale
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
        ξ * hcirc ω (Real.exp (-(s + n))) 0))) :=
      (measurable_const.add (measurable_const.mul
        (hh.measurable_circle _ _ (Real.exp_pos _)))).exp.ennreal_ofReal
    exact normalized_internalDiameter_measurable_and_bound isOpen_ball hsub hmeasD hD _
      hB.aemeasurable (fun _ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (fun _ => ENNReal.ofReal_ne_top)
  apply hcriterion X C hCfin
  · intro n i _
    exact (hnorm n i).1
  · exact hmoment
  · intro n i _
    exact (hnorm n i).2


end HarmonicBalls
