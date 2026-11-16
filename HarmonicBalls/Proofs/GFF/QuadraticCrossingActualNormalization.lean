import HarmonicBalls.Proofs.GFF.PfefferNormalizationMeasurable
import HarmonicBalls.Proofs.GFF.QuadraticCrossingNormalization

/-! # Quadratic crossings with zero and quadratic shift normalizations

For a whole-plane GFF, the simultaneous crossing and crossing-ratio bounds
hold with the Pfeffer normalizations of the zero shift and of the quadratic
shift `z ↦ ‖z‖ ^ 2`. Measurability of these normalizations comes from the
circle averages of the field, and finiteness from positive scale constants.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- The simultaneous crossing bounds with the zero and quadratic shift
normalizations of a whole-plane GFF. -/
theorem IsWholePlaneGFF.quadraticCrossingFamily_simultaneous_pfefferNormalization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D E : Ω → ℂ → ℂ → ℝ} {ξ : ℝ} {c d : ℝ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hpointD : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hpointE : ∀ x y, AEMeasurable (fun ω => E ω x y) P)
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => ‖z‖ ^ 2) x y)
    (htight : ∀ i, PfefferTightAcrossScales P (quadraticCrossingFamily D E
      (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
      (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) i))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Fin 4 → ℝ, (∀ i, 0 < M i) ∧ ∀ r, 0 < r →
      ENNReal.ofReal (1 - ε) ≤ P {ω |
        (∀ i, ENNReal.ofReal (M i)⁻¹ ≤ quadraticCrossingFamily D E
            (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
            (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) i r ω ∧
          quadraticCrossingFamily D E
            (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
            (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) i r ω ≤
            ENNReal.ofReal (M i)) ∧
        ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
          pfefferAcross (D ω) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
          pfefferAcross (E ω) 0 r (2 * r) ∧
        pfefferAcross (E ω) 0 r ((11 / 10 : ℝ) * r) ≤
          ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
            pfefferAcross (D ω) 0 (r / 2) ((6 / 5 : ℝ) * r)} :=
  quadraticCrossingFamily_simultaneous hξ hD hE hpointD hpointE
    (fun _ hr => hgff.aemeasurable_pfefferNormalization_zero ξ c hr)
    (fun _ hr => hgff.aemeasurable_pfefferNormalization_quadratic ξ d hr)
    hscale htight hε hε1

/-- The simultaneous crossing-ratio bounds with the zero and quadratic shift
normalizations of a whole-plane GFF and positive scale constants. -/
theorem IsWholePlaneGFF.quadraticCrossingFamily_ratio_simultaneous_pfefferNormalization
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D E : Ω → ℂ → ℂ → ℝ} {ξ : ℝ} {c d : ℝ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hc : ∀ r, 0 < r → 0 < c r) (hd : ∀ r, 0 < r → 0 < d r)
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (E ω))
    (hpointD : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hpointE : ∀ x y, AEMeasurable (fun ω => E ω x y) P)
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (E ω x y) =
      weylScaling (D ω) ξ (fun z => ‖z‖ ^ 2) x y)
    (htight : ∀ i, PfefferTightAcrossScales P (quadraticCrossingFamily D E
      (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
      (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) i))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Fin 4 → ℝ, (∀ i, 0 < M i) ∧ ∀ r, 0 < r →
      ENNReal.ofReal (1 - ε) ≤ P {ω |
        ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
            (ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1)) ≤
          quadraticCrossingFamily D E
              (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
              (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) 2 r ω /
            quadraticCrossingFamily D E
              (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
              (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) 3 r ω ∧
        quadraticCrossingFamily D E
              (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
              (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) 2 r ω /
            quadraticCrossingFamily D E
              (pfefferNormalization ξ hcirc (fun _ _ => 0) c)
              (pfefferNormalization ξ hcirc (fun _ z => ‖z‖ ^ 2) d) 3 r ω ≤
          ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹} :=
  quadraticCrossingFamily_ratio_simultaneous hξ hD hE hpointD hpointE
    (fun _ hr => hgff.aemeasurable_pfefferNormalization_zero ξ c hr)
    (fun _ hr => hgff.aemeasurable_pfefferNormalization_quadratic ξ d hr)
    (fun r hr => Filter.Eventually.of_forall fun ω =>
      pfefferNormalization_ne_zero_ne_top ξ hcirc _ c ω (hc r hr))
    (fun r hr => Filter.Eventually.of_forall fun ω =>
      pfefferNormalization_ne_zero_ne_top ξ hcirc _ d ω (hd r hr))
    hscale htight hε hε1

end HarmonicBalls
