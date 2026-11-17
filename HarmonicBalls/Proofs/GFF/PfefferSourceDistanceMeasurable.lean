import HarmonicBalls.Proofs.GFF.PfefferRandomNormalizationConsumer

/-! # Point distances of Pfeffer weak LQG metrics

Let `h^ℂ` be a whole-plane GFF and `f` a random continuous function with measurable point evaluations. The field
`h = h^ℂ + f` (`pfefferField`) is a measurable map into the space of pairing functionals with the distribution
σ-algebra `distributionMeasurableSpace`. Hence the pointwise distance measurability in Definition 1.6 of Pfeffer
(`IsPfefferWeakLQGMetric`, see deviation 2 in `HarmonicBalls.Proposed.PfefferMetricScaling`) makes every point
distance `ω ↦ D_h(z, w)` measurable.

This discharges the point distance hypotheses of the simultaneous crossing bounds with random-shift normalizations
for `D = D_{h^ℂ + f}` and `E = D_{h^ℂ + g}`. The metric, Weyl scaling and tightness hypotheses stay explicit.
-/

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- For a random continuous function `f` with measurable point evaluations and a measurable `φ`, the pairing
`ω ↦ ∫ f(ω, x) φ(x) dx` is measurable. -/
theorem measurable_integral_mul_of_continuous_of_measurable {Ω : Type*} [MeasurableSpace Ω]
    {f : Ω → ℂ → ℝ} (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable fun ω => f ω z)
    {φ : ℂ → ℝ} (hφ : Measurable φ) :
    Measurable fun ω => ∫ x, f ω x * φ x := by
  have hjoint : Measurable fun p : Ω × ℂ => f p.1 p.2 :=
    (measurable_uncurry_of_continuous_of_measurable (u := fun x ω => f ω x) hfcont hfmeas).comp
      measurable_swap
  exact ((hjoint.mul (hφ.comp measurable_snd)).stronglyMeasurable.integral_prod_right'
    (ν := volume)).measurable

/-- For a whole-plane GFF `h^ℂ` and a random continuous function `f` with measurable point evaluations, the field
`h^ℂ + f` is measurable for the distribution σ-algebra. -/
theorem IsWholePlaneGFF.measurable_pfefferField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {f : Ω → ℂ → ℝ} (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable fun ω => f ω z) :
    @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace (pfefferField hC f) := by
  refine measurable_iff_comap_le.2 ?_
  unfold distributionMeasurableSpace
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_iSup]
  refine iSup_le fun hφ => ?_
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.1 ((hgff.measurable_pairing φ hφ).add
    (measurable_integral_mul_of_continuous_of_measurable hfcont hfmeas hφ.1.continuous.measurable))

/-- The pointwise distance measurability of a metric assignment `𝔇` makes the point distances of the field
`h^ℂ + f` measurable. -/
theorem IsWholePlaneGFF.measurable_pfefferField_distance {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {f : Ω → ℂ → ℝ} (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable fun ω => f ω z)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : ∀ z w : ℂ, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w) (z w : ℂ) :
    Measurable fun ω => 𝔇 (pfefferField hC f ω) z w :=
  @Measurable.comp Ω ((ℂ → ℝ) → ℝ) ℝ _ distributionMeasurableSpace _ _ _ (h𝔇 z w)
    (hgff.measurable_pfefferField hfcont hfmeas)

/-- For a weak LQG metric in the sense of Pfeffer, the point distances of the field `h^ℂ + f` are measurable. -/
theorem IsPfefferWeakLQGMetric.measurable_pfefferField_distance {ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsPfefferWeakLQGMetric ξ 𝔇)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    {f : Ω → ℂ → ℝ} (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable fun ω => f ω z)
    (z w : ℂ) :
    Measurable fun ω => 𝔇 (pfefferField hC f ω) z w :=
  hgff.measurable_pfefferField_distance hfcont hfmeas h𝔇.2.1 z w

/-- Simultaneous crossing bounds with random continuous shift normalizations for the distances
`D = D_{h^ℂ + f}` and `E = D_{h^ℂ + g}` of a metric assignment with measurable point distances. -/
theorem IsWholePlaneGFF.quadraticCrossingFamily_simultaneous_random_pfefferNormalization_of_measurable_distance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {ξ : ℝ} {c d : ℝ → ℝ}
    {f g : Ω → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable (fun ω => f ω z))
    (hgcont : ∀ ω, Continuous (g ω)) (hgmeas : ∀ z, Measurable (fun ω => g ω z))
    (h𝔇meas : ∀ z w : ℂ, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w)
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (pfefferField hC f ω)))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (pfefferField hC g ω)))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (𝔇 (pfefferField hC g ω) x y) =
      weylScaling (𝔇 (pfefferField hC f ω)) ξ (fun z => ‖z‖ ^ 2) x y)
    (htight : ∀ i, PfefferTightAcrossScales P (quadraticCrossingFamily
      (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
      (pfefferNormalization ξ hcirc f c)
      (pfefferNormalization ξ hcirc g d) i))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Fin 4 → ℝ, (∀ i, 0 < M i) ∧ ∀ r, 0 < r →
      ENNReal.ofReal (1 - ε) ≤ P {ω |
        (∀ i, ENNReal.ofReal (M i)⁻¹ ≤ quadraticCrossingFamily
            (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
            (pfefferNormalization ξ hcirc f c)
            (pfefferNormalization ξ hcirc g d) i r ω ∧
          quadraticCrossingFamily
            (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
            (pfefferNormalization ξ hcirc f c)
            (pfefferNormalization ξ hcirc g d) i r ω ≤
            ENNReal.ofReal (M i)) ∧
        ENNReal.ofReal (Real.exp (ξ * ((19 / 10 : ℝ) * r) ^ 2)) *
          pfefferAcross (𝔇 (pfefferField hC f ω)) 0 ((19 / 10 : ℝ) * r) (2 * r) ≤
          pfefferAcross (𝔇 (pfefferField hC g ω)) 0 r (2 * r) ∧
        pfefferAcross (𝔇 (pfefferField hC g ω)) 0 r ((11 / 10 : ℝ) * r) ≤
          ENNReal.ofReal (Real.exp (ξ * ((11 / 10 : ℝ) * r) ^ 2)) *
            pfefferAcross (𝔇 (pfefferField hC f ω)) 0 (r / 2) ((6 / 5 : ℝ) * r)} :=
  hgff.quadraticCrossingFamily_simultaneous_random_pfefferNormalization hfcont hfmeas hgcont hgmeas hξ hD hE
    (fun x y => (hgff.measurable_pfefferField_distance hfcont hfmeas h𝔇meas x y).aemeasurable)
    (fun x y => (hgff.measurable_pfefferField_distance hgcont hgmeas h𝔇meas x y).aemeasurable)
    hscale htight hε hε1

/-- Simultaneous crossing-ratio bounds with random continuous shift normalizations for the distances
`D = D_{h^ℂ + f}` and `E = D_{h^ℂ + g}` of a metric assignment with measurable point distances. -/
theorem IsWholePlaneGFF.quadraticCrossingFamily_ratio_simultaneous_random_pfefferNormalization_of_measurable_distance
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {ξ : ℝ} {c d : ℝ → ℝ}
    {f g : Ω → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc)
    (hfcont : ∀ ω, Continuous (f ω)) (hfmeas : ∀ z, Measurable (fun ω => f ω z))
    (hgcont : ∀ ω, Continuous (g ω)) (hgmeas : ∀ z, Measurable (fun ω => g ω z))
    (h𝔇meas : ∀ z w : ℂ, Measurable[distributionMeasurableSpace] fun T => 𝔇 T z w)
    (hc : ∀ r, 0 < r → 0 < c r) (hd : ∀ r, 0 < r → 0 < d r)
    (hξ : 0 < ξ)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (pfefferField hC f ω)))
    (hE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (pfefferField hC g ω)))
    (hscale : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (𝔇 (pfefferField hC g ω) x y) =
      weylScaling (𝔇 (pfefferField hC f ω)) ξ (fun z => ‖z‖ ^ 2) x y)
    (htight : ∀ i, PfefferTightAcrossScales P (quadraticCrossingFamily
      (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
      (pfefferNormalization ξ hcirc f c)
      (pfefferNormalization ξ hcirc g d) i))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ M : Fin 4 → ℝ, (∀ i, 0 < M i) ∧ ∀ r, 0 < r →
      ENNReal.ofReal (1 - ε) ≤ P {ω |
        ENNReal.ofReal (Real.exp ((12 / 5 : ℝ) * ξ * r ^ 2)) *
            (ENNReal.ofReal (M 0)⁻¹ / ENNReal.ofReal (M 1)) ≤
          quadraticCrossingFamily
              (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
              (pfefferNormalization ξ hcirc f c)
              (pfefferNormalization ξ hcirc g d) 2 r ω /
            quadraticCrossingFamily
              (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
              (pfefferNormalization ξ hcirc f c)
              (pfefferNormalization ξ hcirc g d) 3 r ω ∧
        quadraticCrossingFamily
              (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
              (pfefferNormalization ξ hcirc f c)
              (pfefferNormalization ξ hcirc g d) 2 r ω /
            quadraticCrossingFamily
              (fun ω => 𝔇 (pfefferField hC f ω)) (fun ω => 𝔇 (pfefferField hC g ω))
              (pfefferNormalization ξ hcirc f c)
              (pfefferNormalization ξ hcirc g d) 3 r ω ≤
          ENNReal.ofReal (M 2) / ENNReal.ofReal (M 3)⁻¹} :=
  hgff.quadraticCrossingFamily_ratio_simultaneous_random_pfefferNormalization hfcont hfmeas hgcont hgmeas hc hd hξ
    hD hE
    (fun x y => (hgff.measurable_pfefferField_distance hfcont hfmeas h𝔇meas x y).aemeasurable)
    (fun x y => (hgff.measurable_pfefferField_distance hgcont hgmeas h𝔇meas x y).aemeasurable)
    hscale htight hε hε1

end HarmonicBalls
