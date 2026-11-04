import HarmonicBalls.Steps.Sec11.ConeGeometry

/-! # Nonzero points in cones -/

namespace HarmonicBalls

open Metric Set

/-- An open sector is closed under addition. -/
theorem openSector_add_mem {v w x y : ℂ} (hx : x ∈ openSector v w)
    (hy : y ∈ openSector v w) : x + y ∈ openSector v w := by
  rcases hx with ⟨a, b, ha, hb, rfl⟩
  rcases hy with ⟨c, d, hc, hd, rfl⟩
  refine ⟨a + c, b + d, add_pos ha hc, add_pos hb hd, ?_⟩
  module

/-- A proper open cone does not contain its vertex. -/
theorem IsOpenCone.zero_not_mem {Q : Set ℂ} (hQ : IsOpenCone Q) : (0 : ℂ) ∉ Q := by
  obtain ⟨_, hopen, hproper, v, w, _, _, hQ⟩ := hQ
  subst Q
  intro hzero
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  apply hproper
  apply Set.eq_univ_iff_forall.mpr
  intro x
  let a : ℝ := ε / (‖x‖ + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have heq : a * (‖x‖ + 1) = ε := by dsimp [a]; field_simp
  have hsmall : ‖a • x‖ < ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha]
    nlinarith [norm_nonneg x]
  have hmem : a • x ∈ openSector v w := hball (by simpa only [Metric.mem_ball, dist_zero_right] using hsmall)
  exact (openSector_smul_mem_iff v w x ha).1 hmem

/-- Every cone in Definition 11.3 contains a nonzero point, including the
complement of a proper open cone. -/
theorem IsCone.exists_ne_zero {Q : Set ℂ} (hQ : IsCone Q) : ∃ x ∈ Q, x ≠ 0 := by
  rcases hQ with h | h
  · obtain ⟨x, hx⟩ := h.1
    exact ⟨x, hx, fun heq => h.zero_not_mem (heq ▸ hx)⟩
  · obtain ⟨x, hx⟩ := h.1
    have hx0 : x ≠ 0 := fun heq => h.zero_not_mem (heq ▸ hx)
    have hznot := h.zero_not_mem
    have hneg : -x ∉ Qᶜ := by
      intro hneg
      obtain ⟨_, _, _, v, w, _, _, heq⟩ := h
      have hsum : x + -x ∈ openSector v w :=
        openSector_add_mem (heq ▸ hx) (heq ▸ hneg)
      have hz : (0 : ℂ) ∈ Qᶜ := by simpa [← heq] using hsum
      exact hznot hz
    exact ⟨-x, by simpa only [mem_compl_iff, not_not] using hneg, neg_ne_zero.mpr hx0⟩

/-- Every cone meets every positive annulus about its vertex. -/
theorem IsCone.coneAt_inter_annulus_nonempty {Q : Set ℂ} (hQ : IsCone Q) (z : ℂ)
    {r : ℝ} (hr : 0 < r) : (annulus z (4 * r) (5 * r) ∩ coneAt Q z).Nonempty := by
  obtain ⟨x, hxQ, hx⟩ := hQ.exists_ne_zero
  exact coneAt_inter_annulus_nonempty_of_cone Q z x r hQ hxQ hx hr

/-- An exterior cone supplies a point outside the set in the outer annulus. -/
theorem outer_annulus_inter_compl_nonempty_of_exterior_cone
    (Q Λ : Set ℂ) (z : ℂ) (r R : ℝ) (hQ : IsCone Q) (hr : 0 < r) (hR : 5 * r ≤ R)
    (hexterior : coneAt Q z ∩ ball z R ⊆ Λᶜ) :
    (annulus z (4 * r) (5 * r) ∩ Λᶜ).Nonempty := by
  obtain ⟨x, hxQ, hx⟩ := hQ.exists_ne_zero
  exact outer_annulus_inter_compl_nonempty_of_exterior_ray Q Λ z x r R hx hr
    (fun _ ha => (hQ.smul_mem_iff x ha).2 hxQ) hR hexterior

end HarmonicBalls
