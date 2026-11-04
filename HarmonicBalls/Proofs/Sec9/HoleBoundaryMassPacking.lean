import HarmonicBalls.Proofs.Sec9.QuantitativeUniqueness
import HarmonicBalls.Proofs.Sec10.ComplementaryHolePacking

/-! # Boundary mass controls complementary components

The common frontier of a subharmonic ball and its cluster has enough mass
for every complementary component of the cluster closure lying in the ball.
This gives an additive bound for finite collections of such components.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The total mass of finitely many cluster-complement components contained
in a comparison ball is at most the mass of the two common frontiers. -/
theorem IsSubharmonicBall.sum_complement_component_mass_le_common_frontier
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t)) (s : Finset (Set ℂ))
    (hcomp : ∀ U ∈ s, U ∈ connectedComponentsIn (closure (cluster μ R z t))ᶜ)
    (hsub : ∀ U ∈ s, U ⊆ A) :
    (∑ U ∈ s, μ U) ≤ μ (frontier (cluster μ R z t) ∩ frontier A) := by
  classical
  have hdis : (↑s : Set (Set ℂ)).PairwiseDisjoint id := by
    intro U hU V hV hne
    exact connectedComponentsIn_pairwise_disjoint _ (hcomp U hU) (hcomp V hV) hne
  have hmeas : ∀ U ∈ s, MeasurableSet U := by
    intro U hU
    obtain ⟨x, hx, rfl⟩ := hcomp U hU
    exact (isClosed_closure.isOpen_compl.connectedComponentIn).measurableSet
  have hsubset : (⋃ U ∈ s, U) ⊆ A \ closure (cluster μ R z t) := by
    intro x hx
    obtain ⟨U, hU, hxU⟩ := mem_iUnion₂.mp hx
    have hUc : U ⊆ (closure (cluster μ R z t))ᶜ := by
      obtain ⟨p, hp, rfl⟩ := hcomp U hU
      exact connectedComponentIn_subset _ _
    exact ⟨hsub U hU hxU, hUc hxU⟩
  have hbound := hA.exterior_mass_le_frontier_sdiff hμ hR ht hz hV hcl hmass hopen
  have hcluster := hA.cluster_subset_of_volumeGrowth hμ hR ht hV hcl hmass
  rw [frontier_sdiff_eq_inter_frontier_of_subset hA.1 hcluster] at hbound
  have hsum : (∑ U ∈ s, μ (id U)) ≤ μ (A \ closure (cluster μ R z t)) := by
    rw [← measure_biUnion_finset hdis hmeas]
    exact measure_mono hsubset
  exact hsum.trans hbound

/-- If each of the selected components contains a ball of radius `r`,
volume growth bounds their number in terms of the common-frontier mass. -/
theorem IsSubharmonicBall.card_complement_components_mul_ball_lower_le_common_frontier
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {A : Set ℂ} {z : ℂ}
    (hA : IsSubharmonicBall μ A z) {R t βm βp : ℝ} (hR : 0 < R) (ht : 0 < t)
    (hz : z ∈ ball (0 : ℂ) R) (hV : VolumeGrowth μ R βm βp)
    (hcl : closure A ⊆ ball 0 R) (hmass : μ A = ENNReal.ofReal t)
    (hopen : IsOpen (cluster μ R z t)) :
    ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ → ∀ s : Finset (Set ℂ),
      (∀ U ∈ s, U ∈ connectedComponentsIn (closure (cluster μ R z t))ᶜ) →
      (∀ U ∈ s, U ⊆ A) → (∀ U ∈ s, ∃ x, ball x r ⊆ U) →
      (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ βm) ≤
        μ (frontier (cluster μ R z t) ∩ frontier A) := by
  classical
  obtain ⟨r₀, hr₀, hvol⟩ := hV.2.2
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr s hcomp hsub hball
  have hlower : ∀ U ∈ s, ENNReal.ofReal (r ^ βm) ≤ μ U := by
    intro U hU
    obtain ⟨x, hx⟩ := hball U hU
    have hxR : x ∈ ball (0 : ℂ) R :=
      hcl (subset_closure (hsub U hU (hx (mem_ball_self hr))))
    exact ((hvol r hr hrr x hxR).1).trans (measure_mono hx)
  have hsum := Finset.sum_le_sum hlower
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum.trans (hA.sum_complement_component_mass_le_common_frontier
    hμ hR ht hz hV hcl hmass hopen s hcomp hsub)

/-- Almost surely, the volume-growth exponent and radius work for every
comparison ball and every finite family of its cluster-complement components. -/
theorem ae_subharmonicBall_complement_component_packing
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ βm : ℝ, ∀ᵐ ω ∂P, 0 < βm ∧ ∀ R : ℝ, 0 < R →
      ∃ r₀ > 0, ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ (A : Set ℂ) (z : ℂ) (t : ℝ), 0 < t → z ∈ ball (0 : ℂ) R →
        closure A ⊆ ball 0 R → IsSubharmonicBall (μ ω) A z →
        μ ω A = ENNReal.ofReal t → ∀ s : Finset (Set ℂ),
        (∀ U ∈ s, U ∈ connectedComponentsIn (closure (cluster (μ ω) R z t))ᶜ) →
        (∀ U ∈ s, U ⊆ A) → (∀ U ∈ s, ∃ x, ball x r ⊆ U) →
        (s.card : ℝ≥0∞) * ENNReal.ofReal (r ^ βm) ≤
          μ ω (frontier (cluster (μ ω) R z t) ∩ frontier A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  refine ⟨βm, ?_⟩
  filter_upwards [hV,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hV hopen
  refine ⟨(hV.2 1 zero_lt_one).1, ?_⟩
  intro R hR
  have hVR := hV.2 R hR
  obtain ⟨r₀, hr₀, hvol⟩ := hVR.2.2
  refine ⟨r₀, hr₀, ?_⟩
  intro r hr hrr A z t ht hz hcl hA hmass s hcomp hsub hball
  have hlower : ∀ U ∈ s, ENNReal.ofReal (r ^ βm) ≤ μ ω U := by
    intro U hU
    obtain ⟨x, hx⟩ := hball U hU
    have hxR : x ∈ ball (0 : ℂ) R :=
      hcl (subset_closure (hsub U hU (hx (mem_ball_self hr))))
    exact ((hvol r hr hrr x hxR).1).trans (measure_mono hx)
  have hsum := Finset.sum_le_sum hlower
  simp only [Finset.sum_const, nsmul_eq_mul] at hsum
  exact hsum.trans (hA.sum_complement_component_mass_le_common_frontier
    hV.1 hR ht hz hVR hcl hmass (hopen t R ht hR z hz).1 s hcomp hsub)

end HarmonicBalls
