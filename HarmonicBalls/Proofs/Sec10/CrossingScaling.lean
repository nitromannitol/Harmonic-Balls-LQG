import HarmonicBalls.Draft.Section10

/-!
# Scaling annular crossing components

Dilation transports crossing components bijectively, preserving their
cardinality. This is the geometric step for comparing crossing estimates in
concentric discs of different radii.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology
open scoped Pointwise

/-- A homeomorphism carrying both boundary spheres to boundary spheres
preserves the crossing property. -/
theorem crossesAnnulus_image_iff (e : ℂ ≃ₜ ℂ) (C : Set ℂ)
    (w w' : ℂ) (r R r' R' : ℝ)
    (hr : e '' sphere w r = sphere w' r')
    (hR : e '' sphere w R = sphere w' R') :
    CrossesAnnulus (e '' C) w' r' R' ↔ CrossesAnnulus C w r R := by
  unfold CrossesAnnulus
  rw [← hr, ← hR, ← e.image_closure, ← Set.image_inter e.injective,
    ← Set.image_inter e.injective]
  simp only [Set.image_nonempty]

/-- A homeomorphism transporting the two boundary spheres maps the family of
crossing components bijectively onto the new family. -/
theorem image_crossingComponents (e : ℂ ≃ₜ ℂ) (Y : Set ℂ)
    (w w' : ℂ) (r R r' R' : ℝ)
    (hr : e '' sphere w r = sphere w' r')
    (hR : e '' sphere w R = sphere w' R') :
    (fun C : Set ℂ => e '' C) '' crossingComponents Y w r R =
      crossingComponents (e '' Y) w' r' R' := by
  ext C
  constructor
  · rintro ⟨D, ⟨⟨x, hx, rfl⟩, hcross⟩, rfl⟩
    refine ⟨⟨e x, ⟨x, hx, rfl⟩, (e.image_connectedComponentIn hx).symm⟩, ?_⟩
    exact (crossesAnnulus_image_iff e _ w w' r R r' R' hr hR).2 hcross
  · rintro ⟨⟨x, hx, rfl⟩, hcross⟩
    obtain ⟨y, hy, rfl⟩ := hx
    refine ⟨connectedComponentIn Y y, ⟨⟨y, hy, rfl⟩, ?_⟩,
      e.image_connectedComponentIn hy⟩
    apply (crossesAnnulus_image_iff e _ w w' r R r' R' hr hR).1
    rw [e.image_connectedComponentIn hy]
    exact hcross

/-- The number of crossing components is invariant under positive dilation. -/
theorem encard_crossingComponents_smul (Y : Set ℂ) (w : ℂ) (r R k : ℝ) (hk : 0 < k) :
    (crossingComponents (k • Y) (k • w) (k * r) (k * R)).encard =
      (crossingComponents Y w r R).encard := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have hr : e '' sphere w r = sphere (k • w) (k * r) := by
    change k • sphere w r = _
    simpa [Real.norm_eq_abs, abs_of_pos hk] using smul_sphere' hk.ne' w r
  have hR : e '' sphere w R = sphere (k • w) (k * R) := by
    change k • sphere w R = _
    simpa [Real.norm_eq_abs, abs_of_pos hk] using smul_sphere' hk.ne' w R
  have hinj : Function.Injective (fun C : Set ℂ => e '' C) := by
    intro A B h
    exact e.injective.image_injective h
  have himage := image_crossingComponents e Y w (k • w) r R (k * r) (k * R) hr hR
  change (crossingComponents (e '' Y) (k • w) (k * r) (k * R)).encard = _
  rw [← himage, hinj.encard_image]

/-- Dilation preserves the exact-radius crossing count used in Lemma 10.1. -/
theorem encard_ball_crossings_smul (Λ : Set ℂ) (w : ℂ) (ρ k : ℝ) (hk : 0 < k) :
    (crossingComponents (k • Λ ∩ ball (k • w) (2 * (k * ρ)))
      (k • w) ((k * ρ) / 3) (2 * (k * ρ))).encard =
    (crossingComponents (Λ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  have hset : k • (Λ ∩ ball w (2 * ρ)) =
      k • Λ ∩ ball (k • w) (2 * (k * ρ)) := by
    change e '' (Λ ∩ ball w (2 * ρ)) = _
    rw [Set.image_inter e.injective]
    change k • Λ ∩ k • ball w (2 * ρ) = _
    rw [_root_.smul_ball hk.ne']
    simp only [Real.norm_eq_abs, abs_of_pos hk]
    congr 2; ring
  have h := encard_crossingComponents_smul (Λ ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) k hk
  rw [hset] at h
  convert h using 1; ring

/-- A pathwise cluster scaling identity transfers the exact-radius crossing
count from the normalized cluster to the cluster in the larger disc. -/
theorem encard_ball_crossings_of_cluster_scale
    (μ ν : Measure ℂ) (z w : ℂ) (t t' ρ k : ℝ) (hk : 0 < k)
    (hscale : cluster ν 1 (k⁻¹ • z) t' = k⁻¹ • cluster μ k z t) :
    (crossingComponents (cluster μ k z t ∩ ball w (2 * ρ)) w (ρ / 3)
      (2 * ρ)).encard =
    (crossingComponents (cluster ν 1 (k⁻¹ • z) t' ∩ ball (k⁻¹ • w) (2 * (ρ / k)))
      (k⁻¹ • w) ((ρ / k) / 3) (2 * (ρ / k))).encard := by
  have h := encard_ball_crossings_smul (cluster ν 1 (k⁻¹ • z) t')
    (k⁻¹ • w) (ρ / k) k hk
  rw [hscale, smul_smul, mul_inv_cancel₀ hk.ne', one_smul,
    smul_smul, mul_inv_cancel₀ hk.ne', one_smul] at h
  rw [← hscale] at h
  have hr : k * (ρ / k) = ρ := by field_simp
  simpa only [hr] using h

end HarmonicBalls
