import HarmonicBalls.Proofs.Sec8.ComparableScaleFrequency
import HarmonicBalls.Proofs.Sec8.ObservedRootReferenceTypicalPoint
import HarmonicBalls.Proofs.Sec8.ObservedBallRootTransfer

/-! # Rooted and singular good-scale frequencies

Observed rooted laws provide regular-measure frequency bounds. A singular Weyl
weight then transfers the bounds away from its insertion point. The rooted
law comparison and fixed-root frequency remain explicit. The imported Section 8
development uses Leonardo Bonanno's whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

/-- Away from the insertion point, singular-measure typical-point frequency
follows from regular-measure frequency without a volume-growth assumption. -/
theorem IsWholePlaneGFF.ae_ae_singular_blockFrequency_of_regular_away_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ}
    (hv : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ≠ 0 → ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      (veryGoodComparableScaleCount (μ ω) β z N₀ (a / 4) b (C₁m / 4) (4 * C₁p)
        (C₂m / 4) (4 * C₂p) C₃ (m / 4) N : ℝ) := by
  have ht := hGFF.ae_ae_singular_of_regular_away_zero hμ hν hv
  filter_upwards [ht, hGFF.ae_singular_weight_of_existing_regular_measure hμ hν]
    with ω hω hweight
  filter_upwards [hω] with z hz hzero
  exact veryGoodComparable_blockFrequency_of_singular_weight hzero hweight hN₀ (hz hzero)

/-- An observable rooted comparison and fixed-root frequency bounds imply the
frequency bound at typical points of the decoded random measure. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_observed_root_reference_cover
    {Ω Ξ F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace F]
    (P : Measure Ω) (ν : Ω → Measure ℂ) (hν : AEMeasurable ν P)
    (X : Ω → F) (hX : Measurable X)
    (decode : F → Measure ℂ) (hdecode : Measurable decode)
    (hdecodefinite : ∀ f, IsLocallyFiniteMeasure (decode f))
    (hdecodeeq : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν ω = c • decode (X ω))
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n)) (hcover : ∀ z, ∃ n, z ∈ B n)
    (hfin : ∀ n, ∀ᵐ ω ∂P, ν ω (B n) ≠ ∞)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (ρ : ℕ → Measure ℂ) (Q : Measure Ξ) [SFinite Q]
    (shift : ℕ → ℂ × Ξ → F) (hshift : ∀ n, Measurable (shift n))
    (R : ℕ → ℂ → Measure F)
    (hrooted : ∀ n, (P.bind fun ω => ((ν ω).restrict (B n)).map
      (fun z => (X ω, z))) ≪ shiftedRootReferenceLaw (ρ n) Q (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, Q.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂(R n z), ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (decode f) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (ν ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m K : ℝ) := by
  let p : F × ℂ → Prop := fun x => ∀ᶠ K : ℕ in atTop,
    (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (decode x.1) β x.2 N₀
      a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)
  have hp : MeasurableSet {x | p x} :=
    measurableSet_eventually_veryGoodComparableScaleCount_joint
      (hdecode.comp measurable_fst) (fun x : F × ℂ => hdecodefinite x.1) measurable_snd
      β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  have ht := ae_ae_of_observed_root_reference_cover P ν hν X hX B hB hcover hfin
    ρ Q shift hshift R hp hrooted hac hfixed
  filter_upwards [ht, hdecodeeq] with ω hω ⟨c, hc, hct, heq⟩
  filter_upwards [hω] with z hz
  simpa only [p, heq, veryGoodComparableScaleCount_smul _ β z N₀
    a b C₁m C₁p C₂m C₂p C₃ m _ hc hct] using hz

universe u

/-- An observed rooted comparison for the regular measure yields the singular
measure frequency estimate under the volume-growth input. -/
theorem IsWholePlaneGFF.ae_ae_singular_blockFrequency_of_regular_root_reference
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {Ξ F : Type*} [MeasurableSpace Ξ] [MeasurableSpace F]
    {P : Measure Ω} {γ α β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) (hνmeas : AEMeasurable ν P)
    (X : Ω → F) (hX : Measurable X)
    (decode : F → Measure ℂ) (hdecode : Measurable decode)
    (hdecodefinite : ∀ f, IsLocallyFiniteMeasure (decode f))
    (hdecodeeq : ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ν ω = c • decode (X ω))
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n)) (hcover : ∀ z, ∃ n, z ∈ B n)
    (hfin : ∀ n, ∀ᵐ ω ∂P, ν ω (B n) ≠ ∞)
    (N₀ : ℕ) (hN₀ : 5 ≤ N₀) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (ρ : ℕ → Measure ℂ) (Q : Measure Ξ) [SFinite Q]
    (shift : ℕ → ℂ × Ξ → F) (hshift : ∀ n, Measurable (shift n))
    (R : ℕ → ℂ → Measure F)
    (hrooted : ∀ n, (P.bind fun ω => ((ν ω).restrict (B n)).map
      (fun z => (X ω, z))) ≪ shiftedRootReferenceLaw (ρ n) Q (shift n))
    (hac : ∀ n, ∀ᵐ z ∂ρ n, Q.map (fun ω => shift n (z, ω)) ≪ R n z)
    (hfixed : ∀ n, ∀ᵐ z ∂ρ n, ∀ᵐ f ∂(R n z), ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (decode f) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        (a / 4) b (C₁m / 4) (4 * C₁p) (C₂m / 4) (4 * C₂p) C₃ (m / 4) K : ℝ) := by
  apply hGFF.ae_ae_singular_blockFrequency_of_regular hgrowth hγ hγ2 hα hμ hν hN₀
  exact ae_ae_veryGoodComparableScaleFrequency_of_observed_root_reference_cover
    P ν hνmeas X hX decode hdecode hdecodefinite hdecodeeq B hB hcover hfin
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit ρ Q shift hshift R hrooted hac hfixed

#print axioms IsWholePlaneGFF.ae_ae_singular_blockFrequency_of_regular_away_zero
#print axioms ae_ae_veryGoodComparableScaleFrequency_of_observed_root_reference_cover
#print axioms IsWholePlaneGFF.ae_ae_singular_blockFrequency_of_regular_root_reference

end HarmonicBalls
