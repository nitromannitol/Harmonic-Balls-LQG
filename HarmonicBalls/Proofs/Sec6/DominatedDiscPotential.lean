import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation
import Mathlib.Analysis.Normed.Module.Convex

/-! # Green potentials of dominated measures on translated discs

Translation transfers the dominated-potential regularity used in the proof of
Lemma 6.10 to discs with arbitrary centre.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Laplacian
open scoped Topology

/-- If a nonempty annulus is contained in a disc, then so is its outer disc. -/
theorem ball_subset_ball_of_annulus_subset_ball {c d : ℂ} {a b R : ℝ}
    (hab : a < b) (hsub : annulus c a b ⊆ ball d R) : ball c b ⊆ ball d R := by
  intro x hx
  have hxb : dist x c < b := hx
  let t : ℝ := (max a (dist x c) + b) / 2
  have hmax : max a (dist x c) < b := max_lt hab hxb
  have htm : max a (dist x c) < t := by dsimp [t]; linarith
  have htb : t < b := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := le_trans (dist_nonneg.trans (le_max_right _ _)) htm.le
  have hs : sphere c t ⊆ ball d R := by
    intro y hy
    apply hsub
    have hy' : dist y c = t := hy
    change dist y c < b ∧ ¬ dist y c ≤ a
    rw [hy']
    exact ⟨htb, not_le_of_gt ((le_max_left _ _).trans_lt htm)⟩
  have hc : closedBall c t ⊆ ball d R := by
    rw [← convexHull_sphere_eq_closedBall c ht0]
    exact convexHull_min hs (convex_ball d R)
  apply hc
  change dist x c ≤ t
  exact (le_max_right _ _).trans htm.le

/-- A restricted dominated measure has a continuous Green potential with the
expected distributional Laplacian on a disc centred at the origin. -/
theorem dominated_restricted_greenPotential_regular {μ ν : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) (hν : ν ≤ μ)
    {A : Set ℂ} {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    (hA : A ⊆ ball (0 : ℂ) R) :
    ContinuousOn (fun x => ∫ y in A, greenFunction (ball 0 R) x y ∂ν) (closedBall 0 R) ∧
    HasLaplacian (fun x => ∫ y in A, greenFunction (ball 0 R) x y ∂ν)
      0 (ν.restrict A) (ball 0 R) := by
  have hrest : (ν.restrict A).restrict (ball 0 R) = ν.restrict A := by
    rw [Measure.restrict_restrict measurableSet_ball, inter_eq_right.mpr hA]
  obtain ⟨hc, hΔ⟩ := dominated_greenPotentialBall hμ hR hV (Measure.restrict_le_self.trans hν)
  rw [hrest] at hc hΔ
  have heqp : greenPotentialBall (ν.restrict A) R =
      fun x => ∫ y in A, greenFunction (ball 0 R) x y ∂ν := by
    funext x
    simp only [greenPotentialBall, Measure.restrict_restrict measurableSet_ball, inter_eq_right.mpr hA]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => greenFunction_ball_comm R y x)
  rw [heqp] at hc hΔ
  exact ⟨hc, hΔ⟩

/-- A restricted measure dominated by a measure with volume growth has a
continuous Green potential and its expected Laplacian on a translated disc. -/
theorem dominated_restricted_greenPotential_center_regular {μ ν : Measure ℂ}
    (hμ : IsLocallyFiniteMeasure μ) (hν : ν ≤ μ) {R r βm βp : ℝ} {c : ℂ}
    (hr : 0 < r) (hV : VolumeGrowth μ R βm βp)
    (hsub : ball c r ⊆ ball 0 R) {A : Set ℂ} (hA : A ⊆ ball c r) :
    ContinuousOn (fun x => ∫ y in A, greenFunction (ball c r) x y ∂ν) (closedBall c r) ∧
    HasLaplacian (fun x => ∫ y in A, greenFunction (ball c r) x y ∂ν)
      0 (ν.restrict A) (ball c r) := by
  let ν' := ν.map (fun z : ℂ => z - c)
  let A' := (fun z : ℂ => z + c) ⁻¹' A
  have hA' : A' ⊆ ball (0 : ℂ) r := by
    intro x hx
    have h := hA hx
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using h
  obtain ⟨hc, hΔ⟩ := dominated_restricted_greenPotential_regular (ν := ν')
    (isLocallyFiniteMeasure_map_sub_right hμ c) (Measure.map_mono hν (by fun_prop)) hr
    (volumeGrowth_map_sub_right hV hsub) hA'
  have hrest : ν'.restrict A' = (ν.restrict A).map (fun z : ℂ => z - c) := by
    let e : ℂ ≃ᵐ ℂ := (Homeomorph.addRight (-c)).toMeasurableEquiv
    have h := e.restrict_map ν A'
    have hpre : (fun z : ℂ => z - c) ⁻¹' A' = A := by
      ext z
      change (z - c) + c ∈ A ↔ z ∈ A
      rw [sub_add_cancel]
    change ν'.restrict A' = (ν.restrict ((fun z : ℂ => z - c) ⁻¹' A')).map
      (fun z : ℂ => z - c) at h
    rw [hpre] at h
    exact h
  have hball : (fun z : ℂ => z + c) '' ball 0 r = ball c r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right, sub_zero] using hx
    · intro hz
      refine ⟨z - c, ?_, sub_add_cancel z c⟩
      simpa only [mem_ball, dist_eq_norm, sub_zero] using hz
  have hq : (fun x => ∫ y in A, greenFunction (ball c r) x y ∂ν) =
      fun x => ∫ y in A', greenFunction (ball 0 r) (x - c) y ∂ν' := by
    funext x
    have h := greenPotential_translate (O := ball 0 r) isOpen_ball (ν.restrict A) c (x - c)
    rw [hball, sub_add_cancel] at h
    rw [← hrest] at h
    exact h
  rw [hq]
  refine ⟨?_, ?_⟩
  · apply hc.comp (continuous_id.sub continuous_const).continuousOn
    intro x hx
    change x - c ∈ closedBall (0 : ℂ) r
    simpa only [mem_closedBall, dist_eq_norm, sub_zero] using hx
  · have h := hasLaplacian_comp_add_right hΔ (-c)
    have hmap : Measure.map (fun z : ℂ => z - (-c)) (ν'.restrict A') = ν.restrict A := by
      rw [hrest, Measure.map_map (by fun_prop) (by fun_prop)]
      simp only [Function.comp_def, sub_neg_eq_add, sub_add_cancel]
      exact Measure.map_id
    have hdomain : (fun z : ℂ => z + -c) ⁻¹' ball 0 r = ball c r := by
      simpa only [sub_eq_add_neg, zero_add] using preimage_ball_sub_right c 0 r
    change HasLaplacian (fun x => ∫ y in A', greenFunction (ball 0 r) (x + -c) y ∂ν')
      (Measure.map (fun z : ℂ => z - (-c)) 0)
      (Measure.map (fun z : ℂ => z - (-c)) (ν'.restrict A')) _ at h
    rw [Measure.map_zero, hmap, hdomain] at h
    simpa only [sub_eq_add_neg] using h

end HarmonicBalls.Section6
