import HarmonicBalls.Proofs.Sec10.PuncturedCircleCrossings

/-! # Cut points of continuous loops

A point of a continuous loop with a unique preimage is not a cut point.
This supplies the elementary direction of the boundary-map argument in
Proposition 10.6 without assuming a conformal extension theorem.
-/

namespace HarmonicBalls

open Set Metric Topology

/-- The circle with one point removed is preconnected. -/
theorem isPreconnected_circle_sdiff_singleton (u : Circle) :
    IsPreconnected ((univ : Set Circle) \ {u}) := by
  have hu : ‖(u : ℂ)‖ = 1 := Circle.norm_coe u
  unfold Circle at u ⊢
  apply (Topology.IsInducing.subtypeVal.isPreconnected_image).mp
  change IsPreconnected (((↑) : (Submonoid.unitSphere ℂ) → ℂ) ''
    ((univ : Set (Submonoid.unitSphere ℂ)) \ {u}))
  have himage : ((↑) : (Submonoid.unitSphere ℂ) → ℂ) ''
      ((univ : Set (Submonoid.unitSphere ℂ)) \ {u}) =
      sphere (0 : ℂ) 1 \ {(u : ℂ)} := by
    rw [Set.image_sdiff Subtype.val_injective, Set.image_univ, Set.image_singleton]
    rw [Subtype.range_val]
    rfl
  rw [himage]
  exact isPreconnected_unit_sphere_sdiff_singleton hu

/-- Removing a point with a unique preimage from a continuous loop leaves
a preconnected set. -/
theorem isPreconnected_loop_sdiff_singleton_of_unique_fiber
    {φ : Circle → ℂ} (hφ : Continuous φ) (u : Circle)
    (huniq : ∀ v : Circle, φ v = φ u → v = u) :
    IsPreconnected (range φ \ {φ u}) := by
  have himage : φ '' ((univ : Set Circle) \ {u}) = range φ \ {φ u} := by
    ext z
    constructor
    · rintro ⟨v, ⟨_, hv⟩, rfl⟩
      refine ⟨⟨v, rfl⟩, ?_⟩
      simpa only [mem_singleton_iff] using fun heq => hv (by simpa using huniq v heq)
    · rintro ⟨⟨v, rfl⟩, hv⟩
      refine ⟨v, ⟨mem_univ v, ?_⟩, rfl⟩
      simp only [mem_singleton_iff] at hv ⊢
      intro h
      exact hv (congrArg φ h)
  rw [← himage]
  exact (isPreconnected_circle_sdiff_singleton u).image φ hφ.continuousOn

/-- A cut point of a continuous loop has at least two distinct preimages. -/
theorem IsCutPoint.exists_two_loop_preimages
    {Γ : Set ℂ} {a : ℂ} (hcut : IsCutPoint Γ a)
    {φ : Circle → ℂ} (hφ : Continuous φ) (hrange : range φ = Γ) :
    ∃ u v : Circle, u ≠ v ∧ φ u = a ∧ φ v = a := by
  have ha : a ∈ range φ := hrange.symm ▸ hcut.1
  obtain ⟨u, hu⟩ := ha
  have hnot : ¬ ∀ v : Circle, φ v = φ u → v = u := by
    intro huniq
    apply hcut.2
    have hpre := isPreconnected_loop_sdiff_singleton_of_unique_fiber hφ u huniq
    simpa [hrange, hu] using hpre
  push Not at hnot
  obtain ⟨v, hv, hne⟩ := hnot
  exact ⟨u, v, hne.symm, hu, hv.trans hu⟩

/-- A simple loop has no cut points. -/
theorem IsSimpleLoop.not_isCutPoint {Γ : Set ℂ} (hΓ : IsSimpleLoop Γ) (a : ℂ) :
    ¬ IsCutPoint Γ a := by
  obtain ⟨φ, hφ, hinj, hrange⟩ := hΓ
  intro hcut
  obtain ⟨u, v, hne, hu, hv⟩ := hcut.exists_two_loop_preimages hφ hrange
  exact hne (hinj (hu.trans hv.symm))

/-- Every simple loop is a compact connected set without cut points. -/
theorem IsSimpleLoop.compact_connected_no_cutPoints {Γ : Set ℂ} (hΓ : IsSimpleLoop Γ) :
    IsCompact Γ ∧ IsConnected Γ ∧ ∀ a : ℂ, ¬ IsCutPoint Γ a := by
  obtain ⟨φ, hφ, hinj, hrange⟩ := hΓ
  refine ⟨hrange ▸ isCompact_range hφ, hrange ▸ isConnected_range hφ, ?_⟩
  exact fun a => (IsSimpleLoop.not_isCutPoint ⟨φ, hφ, hinj, hrange⟩ a)

end HarmonicBalls
