import HarmonicBalls.Defs.Geometry

/-! # A ray meets every positive annulus -/

namespace HarmonicBalls

open Metric Set

/-- An open sector is invariant under positive real dilations. -/
theorem openSector_smul_mem_iff (v w x : ℂ) {a : ℝ} (ha : 0 < a) :
    a • x ∈ openSector v w ↔ x ∈ openSector v w := by
  constructor
  · rintro ⟨c, d, hc, hd, h⟩
    refine ⟨c / a, d / a, div_pos hc ha, div_pos hd ha, ?_⟩
    have hh := congrArg (fun y : ℂ => a⁻¹ • y) h
    simpa [smul_add, smul_smul, div_eq_mul_inv, mul_comm, mul_assoc, ha.ne'] using hh
  · rintro ⟨c, d, hc, hd, rfl⟩
    exact ⟨a * c, a * d, mul_pos ha hc, mul_pos ha hd, by simp [smul_add, mul_assoc]⟩

/-- Cones, including complements of open sectors, are invariant under positive
dilations. -/
theorem IsCone.smul_mem_iff {Q : Set ℂ} (hQ : IsCone Q) (x : ℂ) {a : ℝ} (ha : 0 < a) :
    a • x ∈ Q ↔ x ∈ Q := by
  rcases hQ with h | h
  · obtain ⟨_, _, _, v, w, _, _, rfl⟩ := h
    exact openSector_smul_mem_iff v w x ha
  · obtain ⟨_, _, _, v, w, _, _, heq⟩ := h
    have hh := not_congr (openSector_smul_mem_iff v w x ha)
    rw [← heq] at hh
    simpa only [Set.mem_compl_iff, not_not] using hh

/-- A set containing a full positive ray meets any concentric annulus.
This supplies the exterior-cone witness used in Lemma 11.5. -/
theorem coneAt_inter_annulus_nonempty_of_ray (Q : Set ℂ) (z x : ℂ) (r : ℝ)
    (hx : x ≠ 0) (hr : 0 < r) (hray : ∀ a : ℝ, 0 < a → a • x ∈ Q) :
    (annulus z (4 * r) (5 * r) ∩ coneAt Q z).Nonempty := by
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let a : ℝ := (9 * r / 2) / ‖x‖
  have ha : 0 < a := by dsimp [a]; positivity
  have hdist : dist (a • x + z) z = 9 * r / 2 := by
    rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    dsimp [a]
    field_simp
  refine ⟨a • x + z, ⟨?_, ?_⟩, ⟨a • x, hray a ha, rfl⟩⟩
  · change dist (a • x + z) z < 5 * r
    rw [hdist]
    linarith
  · change ¬ dist (a • x + z) z ≤ 4 * r
    rw [hdist]
    linarith

/-- A cone containing a nonzero point meets every positive annulus about its
vertex. -/
theorem coneAt_inter_annulus_nonempty_of_cone (Q : Set ℂ) (z x : ℂ) (r : ℝ)
    (hQ : IsCone Q) (hxQ : x ∈ Q) (hx : x ≠ 0) (hr : 0 < r) :
    (annulus z (4 * r) (5 * r) ∩ coneAt Q z).Nonempty :=
  coneAt_inter_annulus_nonempty_of_ray Q z x r hx hr
    (fun _ ha => (hQ.smul_mem_iff x ha).2 hxQ)

/-- An exterior positive ray supplies a point outside the set in the outer
annulus whenever the cone-condition radius contains that annulus. -/
theorem outer_annulus_inter_compl_nonempty_of_exterior_ray
    (Q Λ : Set ℂ) (z x : ℂ) (r R : ℝ) (hx : x ≠ 0) (hr : 0 < r)
    (hray : ∀ a : ℝ, 0 < a → a • x ∈ Q) (hR : 5 * r ≤ R)
    (hexterior : coneAt Q z ∩ ball z R ⊆ Λᶜ) :
    (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty := by
  obtain ⟨y, hyann, hycone⟩ := coneAt_inter_annulus_nonempty_of_ray Q z x r hx hr hray
  exact ⟨y, hyann, hexterior ⟨hycone, ball_subset_ball hR hyann.1⟩⟩

end HarmonicBalls
