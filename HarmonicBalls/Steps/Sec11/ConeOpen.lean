import HarmonicBalls.Steps.Sec11.ConeNonzero

/-! # Open subcones of cones -/

namespace HarmonicBalls

open Set

/-- Reflection through the origin commutes with forming an open sector. -/
theorem openSector_neg (v w : ℂ) :
    openSector (-v) (-w) = (fun x : ℂ => -x) '' openSector v w := by
  ext x
  constructor
  · rintro ⟨a, b, ha, hb, hx⟩
    refine ⟨a • v + b • w, ⟨a, b, ha, hb, rfl⟩, ?_⟩
    rw [hx]
    module
  · rintro ⟨y, ⟨a, b, ha, hb, hy⟩, rfl⟩
    refine ⟨a, b, ha, hb, ?_⟩
    rw [hy]
    module

/-- The reflection of a proper open cone is again a proper open cone. -/
theorem IsOpenCone.neg_image {Q : Set ℂ} (hQ : IsOpenCone Q) :
    IsOpenCone ((fun x : ℂ => -x) '' Q) := by
  have hzQ : (0 : ℂ) ∉ Q := hQ.zero_not_mem
  obtain ⟨hne, hopen, _, v, w, hv, hw, heq⟩ := hQ
  refine ⟨hne.image _, ?_, ?_, -v, -w, neg_ne_zero.mpr hv, neg_ne_zero.mpr hw, ?_⟩
  · have hpre : (fun x : ℂ => -x) '' Q = (fun x : ℂ => -x) ⁻¹' Q := by
      ext x
      simp only [mem_image, mem_preimage]
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
      · intro hx
        exact ⟨-x, hx, neg_neg x⟩
    rw [hpre]
    exact hopen.preimage continuous_neg
  · intro hall
    have hz : (0 : ℂ) ∈ (fun x : ℂ => -x) '' Q := by rw [hall]; trivial
    obtain ⟨y, hy, he⟩ := hz
    have hy0 : y = 0 := neg_eq_zero.mp he
    exact hzQ (hy0 ▸ hy)
  · rw [heq, openSector_neg]

/-- A proper open cone and its reflection are disjoint. -/
theorem IsOpenCone.disjoint_neg_image {Q : Set ℂ} (hQ : IsOpenCone Q) :
    Disjoint Q ((fun x : ℂ => -x) '' Q) := by
  apply disjoint_left.mpr
  intro x hx hneg
  obtain ⟨y, hy, rfl⟩ := hneg
  have hzQ : (0 : ℂ) ∉ Q := hQ.zero_not_mem
  obtain ⟨_, _, _, v, w, _, _, heq⟩ := hQ
  have hsum : (-y) + y ∈ openSector v w := openSector_add_mem (heq ▸ hx) (heq ▸ hy)
  have hz : (0 : ℂ) ∈ Q := by simpa [← heq] using hsum
  exact hzQ hz

/-- Every cone, including the complement of an open cone, contains a proper
open cone. -/
theorem IsCone.exists_open_subcone {Q : Set ℂ} (hQ : IsCone Q) :
    ∃ V : Set ℂ, IsOpenCone V ∧ V ⊆ Q := by
  rcases hQ with h | h
  · exact ⟨Q, h, Subset.rfl⟩
  · refine ⟨(fun x : ℂ => -x) '' Qᶜ, h.neg_image, ?_⟩
    intro x hx
    by_contra hn
    have hx' : x ∈ Qᶜ := hn
    exact Set.disjoint_left.mp h.disjoint_neg_image hx' hx

/-- If two directions belong to an open cone, the positive sector they span
is contained in that cone. -/
theorem IsOpenCone.openSector_subset {Q : Set ℂ} (hQ : IsOpenCone Q)
    {v w : ℂ} (hv : v ∈ Q) (hw : w ∈ Q) : openSector v w ⊆ Q := by
  intro x hx
  obtain ⟨a, b, ha, hb, rfl⟩ := hx
  have hQa : a • v ∈ Q := (IsCone.smul_mem_iff (Or.inl hQ) v ha).2 hv
  have hQb : b • w ∈ Q := (IsCone.smul_mem_iff (Or.inl hQ) w hb).2 hw
  obtain ⟨_, _, _, v', w', _, _, heq⟩ := hQ
  rw [heq] at hQa hQb ⊢
  exact openSector_add_mem hQa hQb

/-- Cofinality among open cones already gives cofinality among all cones. -/
theorem cofinal_open_cones_are_cofinal_cones (cones : ℕ → Set ℂ)
    (hsub : ∀ Q : Set ℂ, IsOpenCone Q → ∃ i, cones i ⊆ Q) :
    ∀ Q : Set ℂ, IsCone Q → ∃ i, cones i ⊆ Q := by
  intro Q hQ
  obtain ⟨V, hV, hVQ⟩ := hQ.exists_open_subcone
  obtain ⟨i, hi⟩ := hsub V hV
  exact ⟨i, hi.trans hVQ⟩

end HarmonicBalls
