import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec5.NoEntryTopology

/-! # Complementary components in harmonic-ball comparison

The boundary comparison in Lemma 9.3 forces every complementary component
of the comparison ball's closure either to lie entirely in the harmonic ball
or to be disjoint from it. Any component of the former kind is bounded.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- If the frontier of an open set lies in `K`, every component of `Kᶜ`
is either contained in the open set or disjoint from it. -/
theorem component_subset_or_disjoint_of_frontier_subset
    {A K : Set ℂ} (hA : IsOpen A) (hfront : frontier A ⊆ K) (x : ℂ) :
    connectedComponentIn Kᶜ x ⊆ A ∨ Disjoint (connectedComponentIn Kᶜ x) A := by
  apply IsPreconnected.subset_or_disjoint_of_disjoint_frontier
    isPreconnected_connectedComponentIn hA
  apply disjoint_left.mpr
  intro y hy hyfront
  exact (connectedComponentIn_subset Kᶜ x hy) (hfront hyfront)

/-- A complementary component of the subharmonic ball's closure is either
inside the harmonic ball, hence bounded, or disjoint from that ball. -/
theorem IsHarmonicBallGen.component_bounded_subset_or_disjoint
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] (hμ : IsLocallyFiniteMeasure μ)
    {A B : Set ℂ} {z : ℂ} (hA : IsHarmonicBallGen μ A z)
    (hB : IsSubharmonicBall μ B z) {R βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp)
    (hAcl : closure A ⊆ ball 0 R) (hBcl : closure B ⊆ ball 0 R)
    (hmass : μ.real A = μ.real B) (x : ℂ) :
    (connectedComponentIn (closure B)ᶜ x ⊆ A ∧
      Bornology.IsBounded (connectedComponentIn (closure B)ᶜ x)) ∨
      Disjoint (connectedComponentIn (closure B)ᶜ x) A := by
  have hfront := hA.frontier_subset_closure_of_volumeGrowth hμ hB hR hV hAcl hBcl hmass
  rcases component_subset_or_disjoint_of_frontier_subset hA.1.1 hfront x with hsub | hdis
  · exact Or.inl ⟨hsub, isBounded_ball.subset (hsub.trans (subset_closure.trans hAcl))⟩
  · exact Or.inr hdis

/-- If the harmonic ball is not contained in the regularization of the
comparison ball, some bounded complementary component of its closure lies
inside the harmonic ball. -/
theorem IsHarmonicBallGen.exists_bounded_complement_component_of_not_subset
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] (hμ : IsLocallyFiniteMeasure μ)
    {A B : Set ℂ} {z : ℂ} (hA : IsHarmonicBallGen μ A z)
    (hB : IsSubharmonicBall μ B z) {R βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp)
    (hAcl : closure A ⊆ ball 0 R) (hBcl : closure B ⊆ ball 0 R)
    (hmass : μ.real A = μ.real B) (hne : ¬ A ⊆ interior (closure B)) :
    ∃ U ∈ connectedComponentsIn (closure B)ᶜ,
      U.Nonempty ∧ U ⊆ A ∧ Bornology.IsBounded U := by
  have hnot : ¬ A ⊆ closure B := fun h => hne (hA.1.1.subset_interior_iff.mpr h)
  obtain ⟨x, hxA, hxB⟩ := not_subset.mp hnot
  have hxBC : x ∈ (closure B)ᶜ := hxB
  have hxU : x ∈ connectedComponentIn (closure B)ᶜ x := mem_connectedComponentIn hxBC
  refine ⟨connectedComponentIn (closure B)ᶜ x, ⟨x, hxBC, rfl⟩, ⟨x, hxU⟩, ?_⟩
  rcases hA.component_bounded_subset_or_disjoint hμ hB hR hV hAcl hBcl hmass x with h | h
  · exact h
  · exact ((disjoint_left.mp h) hxU hxA).elim

/-- Almost surely, every failure of harmonic-ball inclusion in the
regularization of a subharmonic ball contains a bounded complementary
component of the latter's closure. -/
theorem ae_harmonicBall_comparison_failure_has_bounded_component
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ) (R : ℝ), 0 < R →
      closure A ⊆ ball 0 R → closure B ⊆ ball 0 R →
      IsHarmonicBallGen (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      (μ ω).real A = (μ ω).real B → ¬ A ⊆ interior (closure B) →
      ∃ U ∈ connectedComponentsIn (closure B)ᶜ,
        U.Nonempty ∧ U ⊆ A ∧ Bornology.IsBounded U := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hV hfull
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro A B z R hR hAcl hBcl hA hB hmass hne
  exact hA.exists_bounded_complement_component_of_not_subset hV.1 hB hR (hV.2 R hR)
    hAcl hBcl hmass hne

end HarmonicBalls
