import HarmonicBalls.Steps.Sec11.ExponentialAnnulusCorridors
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Annular diameter bounds from Borel–Cantelli

Summable probabilities of failure imply eventual exponential annular diameter
bounds. Finiteness at the remaining scales gives a finite random constant.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- An eventual bound by positive finite terms extends to all indices after
multiplication by a finite constant, provided the initial terms are finite. -/
theorem exists_finite_multiplier_of_eventually_le
    (a b : ℕ → ℝ≥0∞) (ha : ∀ n, a n ≠ ∞)
    (hb0 : ∀ n, b n ≠ 0) (hbt : ∀ n, b n ≠ ∞)
    (hevent : ∀ᶠ n in atTop, a n ≤ b n) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n, a n ≤ C * b n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hevent
  let C : ℝ≥0∞ := 1 + ∑ n ∈ Finset.range N, a n / b n
  have hC : C ≠ ∞ := by
    dsimp [C]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.sum_ne_top.mpr (fun n _ => ENNReal.div_ne_top (ha n) (hb0 n))⟩
  refine ⟨C, hC, fun n => ?_⟩
  by_cases hn : n < N
  · have hle : a n / b n ≤ C := by
      calc
        a n / b n ≤ ∑ i ∈ Finset.range N, a i / b i :=
          Finset.single_le_sum (f := fun i : ℕ => a i / b i)
            (fun _ _ => zero_le) (Finset.mem_range.mpr hn)
        _ ≤ C := le_add_self
    calc
      a n = a n / b n * b n := (ENNReal.div_mul_cancel (hb0 n) (hbt n)).symm
      _ ≤ C * b n := by gcongr
  · have hN' : N ≤ n := Nat.le_of_not_gt hn
    calc
      a n ≤ b n := hN n hN'
      _ = 1 * b n := (one_mul _).symm
      _ ≤ C * b n := by gcongr; exact le_add_right le_rfl

/-- Summable exceedance probabilities yield a finite random multiplicative
constant for exponential shell-diameter bounds. The exceedance estimate is an
explicit hypothesis and need not involve measurable events. -/
theorem ae_exponential_annulus_bounds_of_summable_exceedance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (s β : ℝ)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hsum : (∑' n, P {ω | ∃ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∃ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
          internalMetric (D ω) (exponentialAnnulusCorridor s n) x y}) ≠ ∞) :
    ∀ᵐ ω ∂P, ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n, ∀ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∀ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        internalMetric (D ω) (exponentialAnnulusCorridor s n) x y ≤
          C * ENNReal.ofReal (Real.exp (-β * (n : ℝ))) := by
  filter_upwards [hmetric, hnonneg, ae_eventually_notMem hsum] with ω hD hDnonneg hgood
  let a : ℕ → ℝ≥0∞ := fun n =>
    ⨆ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ⨆ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        internalMetric (D ω) (exponentialAnnulusCorridor s n) x y
  let b : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (Real.exp (-β * (n : ℝ)))
  have ha : ∀ n, a n ≠ ∞ := fun n =>
    ne_of_lt (hD.exponentialAnnulusCorridor_diameter_lt_top hDnonneg s n)
  have hb0 : ∀ n, b n ≠ 0 := fun n => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hbt : ∀ n, b n ≠ ∞ := fun _ => ENNReal.ofReal_ne_top
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
    exact le_of_not_gt (fun h => hn ⟨x, hx, y, hy, h⟩)
  obtain ⟨C, hC, hbound⟩ := exists_finite_multiplier_of_eventually_le a b ha hb0 hbt hevent
  refine ⟨C, hC, fun n x hx y hy => ?_⟩
  apply le_trans _ (hbound n)
  dsimp [a]
  apply le_iSup_of_le x
  apply le_iSup_of_le hx
  apply le_iSup_of_le y
  exact le_iSup (fun _ : y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n =>
    internalMetric (D ω) (exponentialAnnulusCorridor s n) x y) hy

/-- Summable exceedance probabilities imply almost sure removal of the
logarithmic singularity from internal distances. All metric and Weyl
identities remain explicit assumptions. -/
theorem ae_internalMetric_sdiff_zero_eq_of_summable_annulus_exceedance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D E : Ω → ℂ → ℂ → ℝ) (s ξ α β : ℝ)
    (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (hgap : ξ * α < β)
    (V : Set ℂ) (hball : Metric.ball (0 : ℂ) (Real.exp (1 - s)) ⊆ V)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hDnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hEnonneg : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ E ω x y)
    (hzero : ∀ᵐ ω ∂P, ∀ x y,
      weylScaling (D ω) ξ 0 x y = ENNReal.ofReal (D ω x y))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => -α * Real.log ‖z‖) x y)
    (hsum : (∑' n, P {ω | ∃ x ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
      ∃ y ∈ geometricShell (Real.exp (-s)) (Real.exp (-1)) n,
        ENNReal.ofReal (Real.exp (-β * (n : ℝ))) <
          internalMetric (D ω) (exponentialAnnulusCorridor s n) x y}) ≠ ∞) :
    ∀ᵐ ω ∂P, ∀ x y : ℂ, x ≠ 0 → y ≠ 0 →
      internalMetric (E ω) (V \ {0}) x y = internalMetric (E ω) V x y := by
  filter_upwards [hD, hE, hEnonneg, hzero, hscale,
    ae_exponential_annulus_bounds_of_summable_exceedance P D s β hD hDnonneg hsum] with
    ω hDω hEω hEωnonneg hzeroω hscaleω hbound
  obtain ⟨C, hC, hbase⟩ := hbound
  intro x y hx hy
  exact hDω.internalMetric_sdiff_zero_eq_of_exponential_annuli hEω hEωnonneg hξ hα
    hgap V hball hzeroω hscaleω hC hbase hx hy

#print axioms ae_internalMetric_sdiff_zero_eq_of_summable_annulus_exceedance
#print axioms exists_finite_multiplier_of_eventually_le
#print axioms ae_exponential_annulus_bounds_of_summable_exceedance

end HarmonicBalls
