import HarmonicBalls.Proofs.Sec8.RootedComparableFrequency

/-! # Singular frequency from a unit-ball rooted law

The observed unit-ball rooted law transfers a measurable frequency event to
singular-measure typical points. The event representation and rooted law
comparison are explicit; no rooted change-of-measure formula is assumed.
The imported Section 8 development uses Leonardo Bonanno's whole-plane GFF
formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

/-- A unit-ball rooted comparison transfers a measurable observed frequency
certificate to typical points of the regular LQG measure. -/
theorem IsWholePlaneGFF.ae_ae_regular_unitBall_blockFrequency_of_root_reference
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {γ β : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (ρ : Measure ℂ) (Q : Measure Ξ) [SFinite Q]
    (shift : ℂ × Ξ → RawMeanZeroTest → ℝ) (hshift : Measurable shift)
    (R : ℂ → Measure (RawMeanZeroTest → ℝ))
    (E : Set ((RawMeanZeroTest → ℝ) × ℂ)) (hE : MeasurableSet E)
    (hrooted : (P.bind fun ω => ((ν ω).restrict (ball 0 1)).map
      (fun z => ((fun φ : RawMeanZeroTest => hC ω φ.1), z))) ≪
        shiftedRootReferenceLaw ρ Q shift)
    (hac : ∀ᵐ z ∂ρ, Q.map (fun ω => shift (z, ω)) ≪ R z)
    (hfixed : ∀ᵐ z ∂ρ, ∀ᵐ f ∂(R z), (f, z) ∈ E)
    (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hcert : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 1 →
      ((fun φ : RawMeanZeroTest => hC ω φ.1), z) ∈ E →
      ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
        (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 1 → ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤
        (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ) := by
  have hfc : (fun ω => fieldCircleAverage 0 (hcirc ω)) = hcirc := by
    funext ω r z
    simp [fieldCircleAverage]
  have hν' : IsLQGMeasure P γ hcirc ν := by
    simpa only [IsLQGMeasureOfField, hfc] using hν
  have hevent := hh.ae_ae_mem_unitBall_of_root_reference hν' ρ Q shift hshift R hE
    hrooted hac hfixed
  filter_upwards [hevent, hcert] with ω he hc
  filter_upwards [he, hc] with z he hc hz
  exact hc hz (he hz)

/-- A regular unit-ball rooted estimate transfers to singular-measure typical
points in that ball away from the insertion point, without volume growth. -/
theorem IsWholePlaneGFF.ae_ae_singular_unitBall_blockFrequency_of_regular
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ}
    (hv : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 1 → ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤
        (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ ball 0 1 → z ≠ 0 → ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        (a / 4) b (C₁m / 4) (4 * C₁p) (C₂m / 4) (4 * C₂p) C₃ (m / 4) K : ℝ) := by
  have ht := hh.ae_ae_singular_of_regular_away_zero hμ hν hv
  filter_upwards [ht, hh.ae_singular_weight_of_existing_regular_measure hμ hν]
    with ω hω hweight
  filter_upwards [hω] with z hz hzball hz0
  exact veryGoodComparable_blockFrequency_of_singular_weight hz0 hweight hN₀ (hz hz0 hzball)

universe u

/-- Under the all-scales volume-growth input, the insertion point is null and
the unit-ball singular frequency transfer holds at almost every point. -/
theorem IsWholePlaneGFF.ae_ae_singular_unitBall_blockFrequency_of_regular_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    {N₀ : ℕ} (hN₀ : 5 ≤ N₀) {a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ}
    (hv : ∀ᵐ ω ∂P, ∀ᵐ z ∂ν ω, z ∈ ball 0 1 → ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤
        (veryGoodComparableScaleCount (ν ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m K : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ ball 0 1 → ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ (veryGoodComparableScaleCount (μ ω) β z N₀
        (a / 4) b (C₁m / 4) (4 * C₁p) (C₂m / 4) (4 * C₂p) C₃ (m / 4) K : ℝ) := by
  have ht := hh.ae_ae_singular_unitBall_blockFrequency_of_regular hμ hν hN₀ hv
  have hnon := Section6.lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ α hC hcirc
    hh hγ hγ2 hα μ hμ
  filter_upwards [ht, hnon] with ω hω hnonω
  have hz : ∀ᵐ z ∂μ ω, z ≠ 0 := by simpa [ae_iff] using hnonω 0
  filter_upwards [hω, hz] with z hωz hz hzball
  exact hωz hzball hz

#print axioms IsWholePlaneGFF.ae_ae_regular_unitBall_blockFrequency_of_root_reference
#print axioms IsWholePlaneGFF.ae_ae_singular_unitBall_blockFrequency_of_regular
#print axioms IsWholePlaneGFF.ae_ae_singular_unitBall_blockFrequency_of_regular_of_volumeGrowth

end HarmonicBalls
