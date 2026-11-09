import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Steps.Sec11.WeylAnnulusBounds
import HarmonicBalls.Steps.Sec11.WeylInversePath

/-!
# Proposition 11.9, bounds for the Weyl-shifted metric (fp-S11d, owner n3)

FIRST-PASS NEW. Wrappers for the shift step of `prop:mass-diam-gen` (corrected paper, lines 3127-3131): with
`h~ = h - (φ/ξ) log(2A/ε)`, the metric of `h~` is the Weyl scaling of the metric of `h` by the weight `e^{-φ c}` (`c = log(2A/ε)`),
so on the open set where `φ ≡ 1` its internal metric is `ε/(2A)` times that of `h`, and on `S₂` (where the weight is at most `1`) it is
at most that of `h`. Also the existence of the open set `O` with `closure(V \ S₂) ⊆ O ⊆ closure O ⊆ W \ S₁`.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- Internal Weyl comparison with the zero-weight identity `weylScaling D ξ 0 = D` (Steps `IsEuclideanLengthMetric.weylScaling_zero`). -/
theorem shifted_internalMetric_le_of_weight {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hEnonneg : ∀ x y, 0 ≤ E x y) {ξ B : ℝ} {f : ℂ → ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    (hweight : ∀ z ∈ U, ξ * f z ≤ B) (x y : ℂ) :
    internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D U x y :=
  hD.internalMetric_weylScaling_le hE hEnonneg hU (hD.weylScaling_zero ξ) hscale hweight x y

/-- If `D(·,·; O) ≤ a` on `A × A`, and `e^B a ≤ δ`, then the Weyl-shifted metric satisfies `E(·,·; O) ≤ δ` on `A × A`. -/
theorem shifted_bound_of_exterior {D E : ℂ → ℂ → ℝ} {O A : Set ℂ} {B a δ : ℝ}
    (hEO : ∀ x y, internalMetric E O x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D O x y)
    (hD : ∀ u ∈ A, ∀ v ∈ A, internalMetric D O u v ≤ ENNReal.ofReal a)
    (hBa : Real.exp B * a ≤ δ) :
    ∀ u ∈ A, ∀ v ∈ A, internalMetric E O u v ≤ ENNReal.ofReal δ := by
  intro u hu v hv
  calc internalMetric E O u v ≤ ENNReal.ofReal (Real.exp B) * internalMetric D O u v := hEO u v
    _ ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal a := by gcongr; exact hD u hu v hv
    _ = ENNReal.ofReal (Real.exp B * a) := (ENNReal.ofReal_mul (Real.exp_pos B).le).symm
    _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hBa

/-- The open set `O` between a compact `K` and an open `U ⊇ K` (paper proof of `prop:mass-diam-gen`, line 3118). -/
theorem exists_open_between_of_compact {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ O : Set ℂ, IsOpen O ∧ K ⊆ O ∧ closure O ⊆ U := by
  obtain ⟨K', hK'c, hKK', hK'U⟩ := exists_compact_between hK hU hKU
  refine ⟨interior K', isOpen_interior, hKK', ?_⟩
  calc closure (interior K') ⊆ closure K' := closure_mono interior_subset
    _ = K' := hK'c.isClosed.closure_eq
    _ ⊆ U := hK'U

end HarmonicBalls
