import HarmonicBalls.Proofs.Sec11.PuncturedMetricOriginExtension
import HarmonicBalls.Steps.Sec11.GeometricPuncturedShells
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Singular-metric locality from geometric annulus estimates

The Section 8 inputs use Leonardo Bonanno's LatticeProb code. Geometric decay
of punctured annulus diameters is an explicit assumption, not proved here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

/-- Geometric upper bounds on punctured annulus diameters permit deletion of the
origin from the internal-metric domain. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_geometric_decay
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (V : Set ℂ)
    {R q : ℝ} (hR : 0 < R) (hq : 0 < q) (hq1 : q < 1)
    {C b : ℝ≥0∞} (hC : C ≠ ∞) (hb : b < 1)
    (hdiam : ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
      internalMetric D (V \ {0}) x y ≤ C * b ^ n)
    {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    internalMetric D (V \ {0}) x y = internalMetric D V x y := by
  apply hD.internalMetric_sdiff_zero_eq_of_geometric_shells V hR hq hq1
    (fun n => C * b ^ n) hdiam ?_ hx hy
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  finiteness [(tsub_pos_iff_lt.2 hb).ne']

/-- A geometric bound at a possibly sample-dependent set of scales yields a
normalized local representative of the singular internal metric. -/
theorem IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_geometric_decay
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V : Set ℂ} (hV : IsOpen V) (hne : (V \ {0}).Nonempty) (hVU : V ⊆ U)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (hdecay : ∀ᵐ ω ∂P, ∃ (R q : ℝ) (C b : ℝ≥0∞),
      0 < R ∧ 0 < q ∧ q < 1 ∧ C ≠ ∞ ∧ b < 1 ∧
      ∀ n, ∀ x ∈ geometricShell R q n, ∀ y ∈ geometricShell R q n,
        internalMetric (D ω) (V \ {0}) x y ≤ C * b ^ n) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y := by
  apply h.exists_modConst_internal_singularMetric_of_point_removal
    𝔇 h𝔇 hD hmetric hV hne hVU ψ hψ hψint
  filter_upwards [hmetric, hdecay] with ω hω hd x hx y hy
  obtain ⟨R, q, C, b, hR, hq, hq1, hC, hb, hdiam⟩ := hd
  have hx0 : x ≠ 0 := by simpa only [mem_singleton_iff] using hx.2
  have hy0 : y ≠ 0 := by simpa only [mem_singleton_iff] using hy.2
  exact hω.internalMetric_sdiff_zero_eq_of_geometric_decay V hR hq hq1 hC hb hdiam hx0 hy0

#print axioms IsEuclideanLengthMetric.internalMetric_sdiff_zero_eq_of_geometric_decay
#print axioms IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_geometric_decay

end HarmonicBalls
