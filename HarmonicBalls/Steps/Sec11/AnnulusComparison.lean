import HarmonicBalls.Defs.Annuli

/-!
# The boundary step in the harmonic comparison chain

The comparison in Lemma 11.6 passes from the boundary of a disk to an
open annulus.  The results here isolate that topological step and assemble
the deterministic inequalities used in the paper.
-/

namespace HarmonicBalls

open Filter Metric Set MeasureTheory

/-- The inner boundary of a nondegenerate annulus is contained in its closure. -/
theorem sphere_subset_closure_annulus (z : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) : sphere z a ⊆ closure (annulus z a b) := by
  intro w hw
  have hfront : w ∈ frontier (closedBall z a) := by
    rw [frontier_closedBall z ha.ne']
    exact hw
  have hc : w ∈ closure (closedBall z a)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hfront
    exact hfront.2
  have hb : w ∈ ball z b := by
    rw [mem_sphere] at hw
    exact mem_ball.mpr (hw.trans_lt hab)
  have h := isOpen_ball.closure_inter ⟨hc, hb⟩
  simpa only [annulus, sdiff_eq, inter_comm] using h

/-- A continuous function on the inner boundary has no larger supremum there
than on the open annulus.  Continuity is needed only at boundary points. -/
theorem iSup_sphere_le_iSup_annulus (z : ℂ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) (u : ℂ → ENNReal)
    (hu : ∀ w ∈ sphere z a, ContinuousAt u w) :
    (⨆ w ∈ sphere z a, u w) ≤ ⨆ w ∈ annulus z a b, u w := by
  refine iSup_le fun w => iSup_le fun hw => ?_
  have hcl := sphere_subset_closure_annulus z ha hab hw
  apply le_of_tendsto_of_frequently (hu w hw)
  exact (mem_closure_iff_frequently.mp hcl).mono fun q hq =>
    le_iSup_of_le q (le_iSup_of_le hq le_rfl)

/-- The deterministic end of the proof of Lemma 11.6: the mass estimate,
the boundary maximum estimate and the outer-annulus estimate combine with
continuity on the intermediate circle. -/
theorem annulus_mass_le_of_comparison_bounds (μ : Measure ℂ) (Λ : Set ℂ)
    (u : ℂ → ENNReal) (z : ℂ) {r : ℝ} (hr : 0 < r)
    (C₁ C₂ : ENNReal)
    (hu : ∀ w ∈ sphere z (4 * r), ContinuousAt u w)
    (hmass : μ (annulus z r (2 * r) ∩ Λ) ≤
      C₁ * (⨆ w ∈ annulus z ((1 / 2) * r) (4 * r), u w))
    (hmax : (⨆ w ∈ annulus z ((1 / 2) * r) (4 * r), u w) ≤
      ⨆ w ∈ sphere z (4 * r), u w)
    (houter : (⨆ w ∈ annulus z (4 * r) (5 * r), u w) ≤
      C₂ * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :
    μ (annulus z r (2 * r) ∩ Λ) ≤
      (C₁ * C₂) * annulusGreenPotentialSup μ z (3 * r) (6 * r) := by
  have hboundary := iSup_sphere_le_iSup_annulus z (show 0 < 4 * r by positivity)
    (show 4 * r < 5 * r by linarith) u hu
  calc
    μ (annulus z r (2 * r) ∩ Λ) ≤ C₁ * _ := hmass
    _ ≤ C₁ * (⨆ w ∈ sphere z (4 * r), u w) := mul_le_mul_right hmax _
    _ ≤ C₁ * (⨆ w ∈ annulus z (4 * r) (5 * r), u w) :=
      mul_le_mul_right hboundary _
    _ ≤ C₁ * (C₂ * annulusGreenPotentialSup μ z (3 * r) (6 * r)) :=
      mul_le_mul_right houter _
    _ = _ := (mul_assoc _ _ _).symm

end HarmonicBalls
