import HarmonicBalls.Proofs.Sec6.AnnulusMassSandwich

/-! # Boundary layers of nearby annuli

A displaced annulus differs from the original only in two thin boundary
layers. For locally finite measures these layers vanish at null circles.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- The symmetric difference of two nearby annuli is contained in the two
closed boundary layers of the reference annulus. -/
theorem annulus_symmDiff_subset_boundary_layers {z w : ℂ} {r R ε : ℝ}
    (hzw : dist w z < ε) :
    (annulus z r R \ annulus w r R) ∪ (annulus w r R \ annulus z r R) ⊆
      {x | r - ε ≤ dist x z ∧ dist x z ≤ r + ε} ∪
      {x | R - ε ≤ dist x z ∧ dist x z ≤ R + ε} := by
  intro x hx
  have ht₁ := dist_triangle x z w
  have ht₂ := dist_triangle x w z
  have hs := dist_comm z w
  simp only [mem_union, Set.mem_sdiff, annulus, mem_ball, mem_closedBall, not_le,
    mem_ofPred_eq] at hx ⊢
  rcases hx with ⟨⟨hxR, hxr⟩, hn⟩ | ⟨⟨hxR, hxr⟩, hn⟩
  · by_cases h : dist x w < R
    · left; have hh : dist x w ≤ r := le_of_not_gt (fun hr => hn ⟨h, hr⟩)
      constructor <;> linarith
    · right; constructor <;> linarith
  · by_cases h : dist x z < R
    · left; have hh : dist x z ≤ r := le_of_not_gt (fun hr => hn ⟨h, hr⟩)
      constructor <;> linarith
    · right; constructor <;> linarith

/-- Open boundary-layer masses converge to zero at a null circle. -/
theorem tendsto_annulus_boundary_layer_mass_zero
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r : ℝ)
    (hnull : μ (sphere z r) = 0) :
    Tendsto (fun n : ℕ => μ (annulus z (r - 1 / ((n : ℝ) + 1))
      (r + 1 / ((n : ℝ) + 1)))) atTop (𝓝 0) := by
  have he : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := tendsto_annulus_mass_of_tendsto_boundaries μ
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => z) atTop (𝓝 z))
    (by simpa using tendsto_const_nhds.sub he)
    (by simpa using tendsto_const_nhds.add he) hnull hnull
  have hempty : annulus z r r = ∅ := sdiff_eq_empty.mpr ball_subset_closedBall
  simpa only [hempty, measure_empty, one_div] using h

/-- At null boundary circles, the mass of the symmetric difference is
uniformly small over all sufficiently nearby centres. -/
theorem exists_nearby_annulus_symmDiff_mass_lt
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] (z : ℂ) (r R : ℝ)
    (hr : μ (sphere z r) = 0) (hR : μ (sphere z R) = 0)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : ℂ, dist w z < ε →
      μ ((annulus z r R \ annulus w r R) ∪
        (annulus w r R \ annulus z r R)) < δ := by
  have hlim := (tendsto_annulus_boundary_layer_mass_zero μ z r hr).add
    (tendsto_annulus_boundary_layer_mass_zero μ z R hR)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      μ (annulus z (r - 1 / ((n : ℝ) + 1)) (r + 1 / ((n : ℝ) + 1))) +
      μ (annulus z (R - 1 / ((n : ℝ) + 1)) (R + 1 / ((n : ℝ) + 1))) < δ := by
    apply hlim.eventually_lt_const
    simpa using hδ
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hsmall
  let e : ℝ := 1 / ((n : ℝ) + 1)
  have he : 0 < e := by dsimp [e]; positivity
  refine ⟨e / 2, by positivity, ?_⟩
  intro w hw
  have hsub := annulus_symmDiff_subset_boundary_layers (r := r) (R := R) (show dist w z < e / 2 from hw)
  have hcover :
      {x : ℂ | r - e / 2 ≤ dist x z ∧ dist x z ≤ r + e / 2} ∪
        {x : ℂ | R - e / 2 ≤ dist x z ∧ dist x z ≤ R + e / 2} ⊆
      annulus z (r - e) (r + e) ∪ annulus z (R - e) (R + e) := by
    intro x hx
    simp only [mem_union, mem_ofPred_eq, annulus, Set.mem_sdiff, mem_ball,
      mem_closedBall, not_le] at hx ⊢
    rcases hx with hx | hx
    · left; constructor <;> linarith [hx.1, hx.2]
    · right; constructor <;> linarith [hx.1, hx.2]
  calc
    μ ((annulus z r R \ annulus w r R) ∪ (annulus w r R \ annulus z r R)) ≤
        μ (annulus z (r - e) (r + e) ∪ annulus z (R - e) (R + e)) :=
      measure_mono (hsub.trans hcover)
    _ ≤ μ (annulus z (r - e) (r + e)) + μ (annulus z (R - e) (R + e)) :=
      measure_union_le _ _
    _ < δ := hn

end HarmonicBalls.Section6
