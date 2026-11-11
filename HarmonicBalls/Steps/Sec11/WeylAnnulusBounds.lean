import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import HarmonicBalls.Steps.Sec11.GeometricPuncturedShells

/-! # Weyl comparison on annular corridors

Bounds for the base metric on punctured open corridors transfer to the Weyl
metric with the exponential of an upper bound for the Weyl exponent.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- On a set bounded away from zero, a nonnegative logarithmic singularity
has a uniform upper bound for its Weyl exponent. -/
theorem logSingularity_weylExponent_le {ξ α r : ℝ} (hξ : 0 ≤ ξ) (hα : 0 ≤ α)
    (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) :
    ξ * (-α * Real.log ‖z‖) ≤ ξ * (-α * Real.log r) := by
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonpos_left (Real.log_le_log hr hz) (neg_nonpos.mpr hα)) hξ

/-- An upper bound for the Weyl exponent on an open set compares the two
internal metrics on that set. -/
theorem IsEuclideanLengthMetric.internalMetric_weylScaling_le
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ B : ℝ} {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ U, ξ * f z ≤ B) (x y : ℂ) :
    internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D U x y := by
  have hnonneg : ∀ x y, 0 ≤ D x y := by
    intro x y
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  apply hD.internalMetric_le_const_mul_of_short_edges hE hEnonneg hU (Real.exp_pos B)
    (fun p hp => hD.path_short_edge_comparison_of_local (Real.exp B) (by
      intro z hz
      obtain ⟨r, hr, hball⟩ := (hD.isOpen_iff U).mp hU z hz
      apply hD.weylScaling_local_edge_bound hnonneg hzero hscale hr
      intro w hw
      exact hweight w (hball w hw)) p hp) x y

/-- Punctured geometric-shell point removal follows from summable weighted
base-metric distances in open annular corridors. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_weyl_corridors
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ : ℝ} {f : ℂ → ℝ} (V : Set ℂ)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    (W : ℕ → Set ℂ) (B : ℕ → ℝ) (c : ℕ → ℝ≥0∞)
    (hWopen : ∀ n, IsOpen (W n)) (hWsub : ∀ n, W n ⊆ V \ {0})
    (hweight : ∀ n z, z ∈ W n → ξ * f z ≤ B n)
    (hbase : ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
      internalMetric D (W n) x y ≤ c n)
    (hsum : (∑' n, ENNReal.ofReal (Real.exp (B n)) * c n) ≠ ∞)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric E (V \ {0}) x y = internalMetric E V x y := by
  apply hE.internalMetric_sdiff_zero_eq_of_geometric_shells V hR hq hq1
    (fun n => ENNReal.ofReal (Real.exp (B n)) * c n) ?_ hsum hx hy
  intro n x hx' y hy'
  calc
    internalMetric E (V \ {0}) x y ≤ internalMetric E (W n) x y :=
      internalMetric_anti E (hWsub n) x y
    _ ≤ ENNReal.ofReal (Real.exp (B n)) * internalMetric D (W n) x y :=
      hD.internalMetric_weylScaling_le hE hEnonneg (hWopen n) hzero hscale
        (hweight n) x y
    _ ≤ ENNReal.ofReal (Real.exp (B n)) * c n := by gcongr; exact hbase n x hx' y hy'

/-- For a nonnegative logarithmic singularity, the Weyl weights in the
annular criterion are determined by the inner radii of the corridors. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_log_corridors
    {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y)
    {ξ α : ℝ} (hξ : 0 ≤ ξ) (hα : 0 ≤ α) (V : Set ℂ)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (hscale : ∀ x y, ENNReal.ofReal (E x y) =
      weylScaling D ξ (fun z => -α * Real.log ‖z‖) x y)
    {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    (W : ℕ → Set ℂ) (r : ℕ → ℝ) (c : ℕ → ℝ≥0∞)
    (hWopen : ∀ n, IsOpen (W n)) (hWsub : ∀ n, W n ⊆ V \ {0})
    (hr : ∀ n, 0 < r n) (hinner : ∀ n z, z ∈ W n → r n ≤ ‖z‖)
    (hbase : ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
      internalMetric D (W n) x y ≤ c n)
    (hsum : (∑' n, ENNReal.ofReal (Real.exp (ξ * (-α * Real.log (r n)))) * c n) ≠ ∞)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric E (V \ {0}) x y = internalMetric E V x y := by
  apply hD.internalMetric_sdiff_zero_eq_of_weyl_corridors hE hEnonneg V hzero hscale
    hR hq hq1 W (fun n => ξ * (-α * Real.log (r n))) c hWopen hWsub ?_ hbase hsum hx hy
  intro n z hz
  exact logSingularity_weylExponent_le hξ hα (hr n) (hinner n z hz)


end HarmonicBalls
