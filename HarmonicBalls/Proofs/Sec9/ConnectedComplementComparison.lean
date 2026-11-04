import HarmonicBalls.Proofs.Sec9.HarmonicBoundaryAssembly
import HarmonicBalls.Proofs.Sec5.NoEntryTopology

/-! # Harmonic-ball comparison and connected complements

The boundary comparison in Lemma 9.3 gives an interior comparison when the
complement of the subharmonic ball's closure is preconnected.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set

universe u

/-- An open set whose frontier is contained in a set lies in its interior if
the complement is preconnected and has a point outside the open set. -/
theorem IsOpen.subset_interior_of_frontier_subset_of_preconnected_compl
    {A K : Set ℂ} (hA : IsOpen A) (hK : IsPreconnected Kᶜ)
    (hfront : frontier A ⊆ K) (hout : ∃ x ∈ Kᶜ, x ∉ A) :
    A ⊆ interior K := by
  have hdis : Disjoint Kᶜ (frontier A) := by
    apply disjoint_left.mpr
    intro x hx hxf
    exact hx (hfront hxf)
  rcases IsPreconnected.subset_or_disjoint_of_disjoint_frontier hK hA hdis with hsub | hdis'
  · obtain ⟨x, hxK, hxA⟩ := hout
    exact (hxA (hsub hxK)).elim
  · apply hA.subset_interior_iff.mpr
    intro x hxA
    by_contra hxK
    exact disjoint_left.mp hdis' hxK hxA

/-- Under volume growth, a harmonic ball is contained in the regularization
of any equal-mass subharmonic ball whose closure has preconnected complement. -/
theorem IsHarmonicBallGen.subset_interior_closure_of_preconnected_compl
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] (hμ : IsLocallyFiniteMeasure μ)
    {A B : Set ℂ} {z : ℂ} (hA : IsHarmonicBallGen μ A z)
    (hB : IsSubharmonicBall μ B z) {R βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp)
    (hAcl : closure A ⊆ ball 0 R) (hBcl : closure B ⊆ ball 0 R)
    (hmass : μ.real A = μ.real B) (hconn : IsPreconnected (closure B)ᶜ) :
    A ⊆ interior (closure B) := by
  have hfront := hA.frontier_subset_closure_of_volumeGrowth hμ hB hR hV hAcl hBcl hmass
  apply IsOpen.subset_interior_of_frontier_subset_of_preconnected_compl hA.1.1 hconn hfront
  let x : ℂ := ((R + 1 : ℝ) : ℂ)
  have hx : x ∉ ball (0 : ℂ) R := by
    have hxnorm : ‖x‖ = R + 1 := by
      change ‖((R + 1 : ℝ) : ℂ)‖ = R + 1
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ R + 1)]
    simp only [mem_ball, dist_zero_right, hxnorm, not_lt]
    linarith
  exact ⟨x, fun hxB => hx (hBcl hxB), fun hxA => hx (hAcl (subset_closure hxA))⟩

/-- Two equal-mass balls that are both harmonic and subharmonic have the
same regularization when both closures have preconnected complements. -/
theorem regularizations_eq_of_harmonic_subharmonic_and_preconnected_compl
    {μ : Measure ℂ} [μ.IsOpenPosMeasure] (hμ : IsLocallyFiniteMeasure μ)
    {A B : Set ℂ} {z : ℂ} (hAh : IsHarmonicBallGen μ A z)
    (hBh : IsHarmonicBallGen μ B z) (hAs : IsSubharmonicBall μ A z)
    (hBs : IsSubharmonicBall μ B z) {R βm βp : ℝ} (hR : 0 < R)
    (hV : VolumeGrowth μ R βm βp)
    (hAcl : closure A ⊆ ball 0 R) (hBcl : closure B ⊆ ball 0 R)
    (hmass : μ.real A = μ.real B) (hconnA : IsPreconnected (closure A)ᶜ)
    (hconnB : IsPreconnected (closure B)ᶜ) :
    interior (closure A) = interior (closure B) := by
  have hAB := hAh.subset_interior_closure_of_preconnected_compl hμ hBs hR hV
    hAcl hBcl hmass hconnB
  have hBA := hBh.subset_interior_closure_of_preconnected_compl hμ hAs hR hV
    hBcl hAcl hmass.symm hconnA
  have hcl : closure A = closure B := Subset.antisymm
    (closure_minimal (hAB.trans interior_subset) isClosed_closure)
    (closure_minimal (hBA.trans interior_subset) isClosed_closure)
  rw [hcl]

/-- The comparison holds simultaneously for all harmonic and subharmonic
balls on the LQG volume-growth event. -/
theorem ae_harmonicBall_subset_regularized_of_preconnected_compl
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ) (R : ℝ), 0 < R →
      closure A ⊆ ball 0 R → closure B ⊆ ball 0 R →
      IsHarmonicBallGen (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      (μ ω).real A = (μ ω).real B → IsPreconnected (closure B)ᶜ →
      A ⊆ interior (closure B) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hV hfull
  let : (μ ω).IsOpenPosMeasure := ⟨fun U hU hne => (hfull U hU hne).ne'⟩
  intro A B z R hR hAcl hBcl hA hB hmass hconn
  exact hA.subset_interior_closure_of_preconnected_compl hV.1 hB hR (hV.2 R hR)
    hAcl hBcl hmass hconn

end HarmonicBalls
