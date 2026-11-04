import HarmonicBalls.Proofs.Sec10.NestedContinuumCrossing

/-!
# Annular crossings of path-connected continua

A path joining the two boundary circles contains an open subpath inside the
annulus whose closure meets both circles.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- A path-connected compact set crossing two circles has a component in the
open annulus which crosses both circles. -/
theorem IsPathConnected.exists_annular_component_crossing
    {K : Set ℂ} (hK : IsPathConnected K) (hKcompact : IsCompact K)
    (w : ℂ) {r R : ℝ} (hrR : r < R) (hcross : CrossesAnnulus K w r R) :
    (crossingComponents (K ∩ annulus w r R) w r R).Nonempty := by
  obtain ⟨⟨p, hp, hpr⟩, ⟨q, hq, hqR⟩⟩ := hcross
  have hpK : p ∈ K := by simpa only [hKcompact.isClosed.closure_eq] using hp
  have hqK : q ∈ K := by simpa only [hKcompact.isClosed.closure_eq] using hq
  obtain ⟨γ, hγK⟩ := hK.joinedIn p hpK q hqK
  let f : ℝ → ℝ := fun t => dist (γ.extend t) w
  have hf : Continuous f := γ.continuous_extend.dist continuous_const
  have hf0 : f 0 = r := by simpa [f, γ.extend_zero] using mem_sphere.mp hpr
  have hf1 : f 1 = R := by simpa [f, γ.extend_one] using mem_sphere.mp hqR
  let T : Set ℝ := Icc 0 1 ∩ f ⁻¹' {R}
  have hTc : IsCompact T := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_singleton.preimage hf)) inter_subset_left
  have hTne : T.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, hf1⟩⟩
  obtain ⟨t, ht⟩ := hTc.exists_isLeast hTne
  have ht0 : 0 ≤ t := ht.1.1.1
  have ht1 : t ≤ 1 := ht.1.1.2
  have hft : f t = R := ht.1.2
  let S : Set ℝ := Icc 0 t ∩ f ⁻¹' {r}
  have hSc : IsCompact S := isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter (isClosed_singleton.preimage hf)) inter_subset_left
  have hSne : S.Nonempty := ⟨0, ⟨⟨le_rfl, ht0⟩, hf0⟩⟩
  obtain ⟨s, hs⟩ := hSc.exists_isGreatest hSne
  have hs0 : 0 ≤ s := hs.1.1.1
  have hst : s < t := by
    have hle := hs.1.1.2
    have hne : s ≠ t := by intro heq; subst s; have : f t = r := hs.1.2; linarith
    exact lt_of_le_of_ne hle hne
  have hfs : f s = r := hs.1.2
  have hinside : ∀ u ∈ Ioo s t, r < f u ∧ f u < R := by
    intro u hu
    constructor
    · by_contra hn
      have hle : f u ≤ r := le_of_not_gt hn
      obtain ⟨v, hv, hvf⟩ := intermediate_value_Icc hu.2.le hf.continuousOn
        (show r ∈ Icc (f u) (f t) from ⟨hle, by rw [hft]; exact hrR.le⟩)
      have hvS : v ∈ S := ⟨⟨hs0.trans (hu.1.le.trans hv.1), hv.2⟩, hvf⟩
      have := hs.2 hvS
      linarith [hv.1, hu.1]
    · by_contra hn
      have hle : R ≤ f u := le_of_not_gt hn
      obtain ⟨v, hv, hvf⟩ := intermediate_value_Icc hu.1.le hf.continuousOn
        (show R ∈ Icc (f s) (f u) from ⟨by rw [hfs]; exact hrR.le, hle⟩)
      have hvT : v ∈ T := ⟨⟨hs0.trans hv.1, hv.2.trans (hu.2.le.trans ht1)⟩, hvf⟩
      have := ht.2 hvT
      linarith [hv.2, hu.2]
  let A : Set ℂ := γ.extend '' Ioo s t
  have hAsub : A ⊆ K ∩ annulus w r R := by
    rintro x ⟨u, hu, rfl⟩
    have huI : u ∈ Icc (0 : ℝ) 1 := ⟨hs0.trans hu.1.le, hu.2.le.trans ht1⟩
    refine ⟨?_, mem_ball.mpr (hinside u hu).2, ?_⟩
    · rw [γ.extend_apply huI]
      exact hγK ⟨u, huI⟩
    · rw [mem_closedBall, not_le]
      exact (hinside u hu).1
  have hAconn : IsPreconnected A := isPreconnected_Ioo.image _ γ.continuous_extend.continuousOn
  let u := (s + t) / 2
  have hu : u ∈ Ioo s t := ⟨by dsimp [u]; linarith, by dsimp [u]; linarith⟩
  let x := γ.extend u
  have hxA : x ∈ A := ⟨u, hu, rfl⟩
  let D := connectedComponentIn (K ∩ annulus w r R) x
  have hAD : A ⊆ D := hAconn.subset_connectedComponentIn hxA hAsub
  have hscl : γ.extend s ∈ closure A := by
    apply image_closure_subset_closure_image γ.continuous_extend
    exact ⟨s, by rw [closure_Ioo hst.ne]; exact ⟨le_rfl, hst.le⟩, rfl⟩
  have htcl : γ.extend t ∈ closure A := by
    apply image_closure_subset_closure_image γ.continuous_extend
    exact ⟨t, by rw [closure_Ioo hst.ne]; exact ⟨hst.le, le_rfl⟩, rfl⟩
  refine ⟨D, ⟨⟨x, hAsub hxA, rfl⟩, ?_⟩⟩
  exact ⟨⟨γ.extend s, closure_mono hAD hscl, mem_sphere.mpr hfs⟩,
    ⟨γ.extend t, closure_mono hAD htcl, mem_sphere.mpr hft⟩⟩

end HarmonicBalls
