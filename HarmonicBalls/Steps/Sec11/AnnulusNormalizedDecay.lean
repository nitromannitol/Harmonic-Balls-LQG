import HarmonicBalls.Steps.Sec11.AnnulusBorelCantelli

/-! # Annular decay with a random normalization

The metric estimates at small scales naturally involve a random circle-average
normalization. A finite normalization can be absorbed into the random
constant after Borel–Cantelli, without a tail estimate for the normalization.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Summable normalized exceedance probabilities give an almost sure
exponential diameter bound with a finite random constant. -/
theorem ae_exponential_annulus_bounds_of_normalized_exceedance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (s β : ℝ)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hA : ∀ᵐ ω ∂P, A ω ≠ ∞)
    (hsum : (∑' n, P {ω | ∃ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∃ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
          internalMetric (D ω) (exponentialAnnulusCorridor s n) x y}) ≠ ∞) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n, ∀ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∀ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        internalMetric (D ω) (exponentialAnnulusCorridor s n) x y ≤
          C * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) := by
  filter_upwards [hmetric, hnonneg, hA, ae_eventually_notMem hsum] with ω hD hDnonneg hAω hgood
  let a : ℕ → ℝ≥0∞ := fun n =>
    ⨆ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ⨆ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        internalMetric (D ω) (exponentialAnnulusCorridor s n) x y
  let b : ℕ → ℝ≥0∞ := fun n =>
    (1 + A ω) * ENNReal.ofReal (Real.exp (-β * (n : ℝ)))
  have ha : ∀ n, a n ≠ ∞ := fun n =>
    ne_of_lt (hD.exponentialAnnulusCorridor_diameter_lt_top hDnonneg s n)
  have hb0 : ∀ n, b n ≠ 0 := by
    intro n
    exact mul_ne_zero (by simp) (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hbt : ∀ n, b n ≠ ∞ := by
    intro n
    exact ENNReal.mul_ne_top (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hAω⟩)
      ENNReal.ofReal_ne_top
  have hevent : ∀ᶠ n in atTop, a n ≤ b n := by
    filter_upwards [hgood] with n hn
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    apply iSup_le
    intro y
    apply iSup_le
    intro hy
    calc
      _ ≤ A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) :=
        le_of_not_gt (fun h => hn ⟨x, hx, y, hy, h⟩)
      _ ≤ b n := by dsimp [b]; gcongr; exact le_add_left le_rfl
  obtain ⟨C, hC, hbound⟩ := exists_finite_multiplier_of_eventually_le a b ha hb0 hbt hevent
  refine ⟨C * (1 + A ω), ENNReal.mul_ne_top hC
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hAω⟩), fun n x hx y hy => ?_⟩
  have hxy : internalMetric (D ω) (exponentialAnnulusCorridor s n) x y ≤ a n := by
    dsimp [a]
    apply le_iSup_of_le x
    apply le_iSup_of_le hx
    apply le_iSup_of_le y
    exact le_iSup (fun _ : y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n =>
      internalMetric (D ω) (exponentialAnnulusCorridor s n) x y) hy
  exact le_trans hxy (by simpa only [b, mul_assoc] using hbound n)

/-- A summable normalized annular exceedance estimate implies almost sure
puncture removal for a logarithmically Weyl-scaled metric. -/
theorem ae_internalMetric_sdiff_zero_eq_of_normalized_annulus_exceedance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D E : Ω → ℂ → ℂ → ℝ) (A : Ω → ℝ≥0∞) (s ξ α β : ℝ)
    (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (hgap : ξ * α < β)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hA : ∀ᵐ ω ∂P, A ω ≠ ∞)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y)
    (hsum : (∑' n, P {ω | ∃ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∃ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        A ω * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
          internalMetric (D ω) (exponentialAnnulusCorridor s n) x y}) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
      internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  filter_upwards [hD, hE, hEnonneg, hzero, hscale,
    ae_exponential_annulus_bounds_of_normalized_exceedance P D A s β hD hDnonneg hA hsum] with
    ω hDω hEω hEωnonneg hzeroω hscaleω hbound
  obtain ⟨C, hC, hbase⟩ := hbound
  intro x y hx hy
  exact hDω.internalMetric_sdiff_zero_eq_of_exponential_annuli hEω hEωnonneg hξ hα
    hgap V hball hzeroω hscaleω hC hbase hx hy


end HarmonicBalls
