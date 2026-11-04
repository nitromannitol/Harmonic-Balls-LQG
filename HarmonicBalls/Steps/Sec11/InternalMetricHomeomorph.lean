import HarmonicBalls.Defs.LQGMetric

/-! # Transport of internal distances by homeomorphisms -/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- Pulling a distance back along a continuous map preserves the length of
the corresponding mapped path. -/
theorem pathLength_comp_continuous (D : ℂ → ℂ → ℝ) {f : ℂ → ℂ}
    (hf : Continuous f) {x y : ℂ} (p : Path x y) :
    pathLength (fun x y => D (f x) (f y)) p = pathLength D (p.map hf) := by
  unfold pathLength curveLength
  apply iSup_congr
  intro q
  apply Finset.sum_congr rfl
  intro i hi
  rw [Path.extend_apply p (q.2.2.2 (i + 1)), Path.extend_apply p (q.2.2.2 i),
    Path.extend_apply (p.map hf) (q.2.2.2 (i + 1)),
    Path.extend_apply (p.map hf) (q.2.2.2 i)]
  rfl

/-- A continuous map sends paths in a set to paths in its image, so its
pullback internal distance dominates the distance in the image. -/
theorem internalMetric_image_le (D : ℂ → ℂ → ℝ) {f : ℂ → ℂ}
    (hf : Continuous f) (U : Set ℂ) (x y : ℂ) :
    internalMetric D (f '' U) (f x) (f y) ≤
      internalMetric (fun x y => D (f x) (f y)) U x y := by
  unfold internalMetric
  refine le_iInf fun p => le_iInf fun hp => ?_
  rw [pathLength_comp_continuous D hf p]
  exact iInf_le_of_le (p.map hf) (iInf_le_of_le (fun t => ⟨p t, hp t, rfl⟩) le_rfl)

/-- A homeomorphism transports internal distances exactly, even when no path
in the domain joins the endpoints. -/
theorem internalMetric_comp_homeomorph (D : ℂ → ℂ → ℝ) (e : ℂ ≃ₜ ℂ)
    (U : Set ℂ) (x y : ℂ) :
    internalMetric (fun x y => D (e x) (e y)) U x y =
      internalMetric D (e '' U) (e x) (e y) := by
  refine le_antisymm ?_ (internalMetric_image_le D e.continuous U x y)
  have h := internalMetric_image_le (fun x y => D (e x) (e y))
    e.symm.continuous (e '' U) (e x) (e y)
  have hU : e.symm '' (e '' U) = U := by
    ext v
    simp only [mem_image]
    constructor
    · rintro ⟨_, ⟨w, hw, rfl⟩, hv⟩
      rw [e.symm_apply_apply] at hv
      exact hv ▸ hw
    · intro hv
      exact ⟨e v, ⟨v, hv, rfl⟩, e.symm_apply_apply v⟩
  simpa only [e.apply_symm_apply, e.symm_apply_apply, hU] using h

/-- A homeomorphism transports the set-to-set distance under pullback. -/
theorem setDist_comp_homeomorph (D : ℂ → ℂ → ℝ) (e : ℂ ≃ₜ ℂ)
    (A B : Set ℂ) :
    setDist (fun x y => D (e x) (e y)) A B = setDist D (e '' A) (e '' B) := by
  unfold setDist
  congr 1
  ext v
  simp only [mem_image2, mem_image]
  constructor
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨e x, ⟨x, hx, rfl⟩, e y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, rfl⟩

/-- A homeomorphism transports the supremum of internal distances from a
fixed point to a set. -/
theorem iSup_internalMetric_comp_homeomorph (D : ℂ → ℂ → ℝ) (e : ℂ ≃ₜ ℂ)
    (U A : Set ℂ) (x : ℂ) :
    (⨆ y ∈ A, internalMetric (fun x y => D (e x) (e y)) U x y) =
      ⨆ y ∈ e '' A, internalMetric D (e '' U) (e x) y := by
  simp only [internalMetric_comp_homeomorph, iSup_image]

/-- A homeomorphism transports the internal diameter of any set. -/
theorem iSup_iSup_internalMetric_comp_homeomorph (D : ℂ → ℂ → ℝ) (e : ℂ ≃ₜ ℂ)
    (U A : Set ℂ) :
    (⨆ x ∈ A, ⨆ y ∈ A, internalMetric (fun x y => D (e x) (e y)) U x y) =
      ⨆ x ∈ e '' A, ⨆ y ∈ e '' A, internalMetric D (e '' U) x y := by
  simp only [internalMetric_comp_homeomorph, iSup_image]

end HarmonicBalls
