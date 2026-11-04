import HarmonicBalls.Proofs.Sec11.PuncturedMetricExhaustionLocality
import HarmonicBalls.Steps.Sec11.DenseInternalMetricVersions

/-! # Conditional extension across the puncture

The Section 8 inputs use Leonardo Bonanno's LatticeProb code. The equality of
punctured and unpunctured distances is an explicit hypothesis, not proved here.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-- If deleting the origin preserves the internal distances between nonzero
points, punctured locality extends to all points by metric continuity. -/
theorem IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_point_removal
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
    (hremove : ∀ᵐ ω ∂P, ∀ x ∈ V \ {0}, ∀ y ∈ V \ {0},
      internalMetric (D ω) (V \ {0}) x y = internalMetric (D ω) V x y) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y := by
  obtain ⟨c, F, hc, hF, hFeq⟩ := h.exists_modConst_internal_singularMetric_punctured
    𝔇 h𝔇 hD hmetric hV hne hVU ψ hψ hψint
  have hdense : V ⊆ closure (V \ {0}) := by
    simpa only [sdiff_eq] using (dense_compl_singleton (0 : ℂ)).open_subset_closure_inter hV
  have hmetric' : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => c ω * D ω x y) := by
    filter_upwards [hmetric, hc] with ω hω hcω
    exact hω.const_mul hcω
  have hFeq' : ∀ᵐ ω ∂P, ∀ x ∈ V \ {0}, ∀ y ∈ V \ {0},
      internalMetric (fun x y => c ω * D ω x y) V x y = F ω x y := by
    filter_upwards [hFeq, hremove, hc] with ω hf hr hcω x hx y hy
    rw [internalMetric_const_mul (D ω) hcω V x y, ← hr x hx y hy,
      ← internalMetric_const_mul (D ω) hcω (V \ {0}) x y]
    exact hf x hx y hy
  obtain ⟨G, hG, hGeq⟩ := exists_internalMetric_version_of_dense
    (Section6.fieldSigmaAlgebraModConst α hC U) hV hdense hmetric' F hF hFeq'
  exact ⟨c, G, hc, hG, hGeq⟩

#print axioms IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_point_removal

end HarmonicBalls
