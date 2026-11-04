import HarmonicBalls.Proofs.Sec10.OneSidedContinuumCrossings

/-!
# Crossing a strictly smaller concentric annulus

A compact continuum crossing two circles has a component in the larger open
annulus crossing any strictly smaller concentric annulus. This leaves open
whether a single such component must meet the two original circles.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- A compact continuum crossing from `r` to `R` has an annular component
crossing from `a` to `b` whenever `r < a < b < R`. -/
theorem IsConnected.exists_annular_component_crossing_smaller
    {K : Set ℂ} (hK : IsConnected K) (hKcompact : IsCompact K)
    (w : ℂ) {r a b R : ℝ} (hra : r < a) (hab : a < b) (hbR : b < R)
    (hcross : CrossesAnnulus K w r R) :
    ∃ D ∈ connectedComponentsIn (K ∩ annulus w r R), CrossesAnnulus D w a b := by
  obtain ⟨⟨p, hpcl, hpr⟩, ⟨q, hqcl, hqR⟩⟩ := hcross
  have hpK : p ∈ K := by simpa only [hKcompact.isClosed.closure_eq] using hpcl
  have hqK : q ∈ K := by simpa only [hKcompact.isClosed.closure_eq] using hqcl
  have hpb : p ∈ ball w b := mem_ball.mpr (by rw [mem_sphere.mp hpr]; linarith)
  have hqout : q ∉ ball w b := by
    intro hq
    have := mem_ball.mp hq
    rw [mem_sphere.mp hqR] at this
    linarith
  let C := connectedComponentIn (K ∩ ball w b) p
  have hpC : p ∈ C := mem_connectedComponentIn ⟨hpK, hpb⟩
  have hCsub : C ⊆ K ∩ ball w b := connectedComponentIn_subset _ p
  obtain ⟨y, hycl, hyK, hyout⟩ :=
    IsConnected.closure_component_inter_open_meets_compl hK hKcompact isOpen_ball
      ⟨q, hqK, hqout⟩ ⟨hpK, hpb⟩
  have hclsub : closure C ⊆ K ∩ closedBall w b :=
    closure_minimal (fun z hz => ⟨(hCsub hz).1, ball_subset_closedBall (hCsub hz).2⟩)
      (hKcompact.isClosed.inter isClosed_closedBall)
  have hyb : y ∈ sphere w b := mem_sphere.mpr (le_antisymm
    (mem_closedBall.mp (hclsub hycl).2) (le_of_not_gt (fun hlt => hyout (mem_ball.mpr hlt))))
  have hCcross : CrossesAnnulus C w r b :=
    ⟨⟨p, subset_closure hpC, hpr⟩, ⟨y, hycl, hyb⟩⟩
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr ⟨hpK, hpb⟩
  obtain ⟨z, hzC, hza⟩ :=
    IsPreconnected.exists_mem_sphere_of_crosses hCconn.isPreconnected hra hab hCcross
  let L := closure C
  have hLcompact : IsCompact L :=
    (isCompact_closedBall w b).of_isClosed_subset isClosed_closure (fun z hz => (hclsub hz).2)
  have hLconn : IsConnected L := hCconn.closure
  have hzL : z ∈ L := subset_closure hzC
  have hyL : y ∈ L := hycl
  let E := connectedComponentIn (L ∩ (closedBall w a)ᶜ) y
  have hEcross : CrossesAnnulus E w a b :=
    IsConnected.exterior_component_crosses_of_outer_point hLconn hLcompact w hab
      ⟨z, hzL, hza⟩ hyL hyb
  have hyext : y ∈ (closedBall w a)ᶜ := by
    rw [mem_compl_iff, mem_closedBall, not_le, mem_sphere.mp hyb]
    exact hab
  have hEsub : E ⊆ K ∩ annulus w r R := by
    intro v hv
    have hvL := (connectedComponentIn_subset _ y hv).1
    have hvext := (connectedComponentIn_subset _ y hv).2
    have hvb : dist v w ≤ b := mem_closedBall.mp (hclsub hvL).2
    have hva : a < dist v w := by simpa only [mem_compl_iff, mem_closedBall, not_le] using hvext
    refine ⟨(hclsub hvL).1, mem_ball.mpr (lt_of_le_of_lt hvb hbR), ?_⟩
    rw [mem_closedBall, not_le]
    exact hra.trans hva
  have hyann : y ∈ K ∩ annulus w r R := hEsub (mem_connectedComponentIn ⟨hyL, hyext⟩)
  let D := connectedComponentIn (K ∩ annulus w r R) y
  have hED : E ⊆ D :=
    isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn ⟨hyL, hyext⟩) hEsub
  have hDcross : CrossesAnnulus D w a b := by
    obtain ⟨⟨u, hu, hua⟩, ⟨v, hv, hvb⟩⟩ := hEcross
    exact ⟨⟨u, closure_mono hED hu, hua⟩, ⟨v, closure_mono hED hv, hvb⟩⟩
  exact ⟨D, ⟨y, hyann, rfl⟩, hDcross⟩

/-- Each crossing component in a ball of a closed set contains an annular
component crossing every specified strictly smaller annulus. The annular
component may depend on the two smaller radii. -/
theorem closed_ball_crossing_contains_smaller_annular_crossing
    {F C : Set ℂ} (hF : IsClosed F) (w : ℂ) {r a b R : ℝ}
    (hra : r < a) (hab : a < b) (hbR : b < R)
    (hC : C ∈ crossingComponents (F ∩ ball w R) w r R) :
    ∃ D ∈ connectedComponentsIn (F ∩ annulus w r R),
      D ⊆ C ∧ CrossesAnnulus D w a b := by
  have hrR : r < R := hra.trans (hab.trans hbR)
  obtain ⟨hcompact, hconn, hclsub, _, hcross⟩ :=
    closed_ball_crossing_compact_continuum hF w hrR hC
  obtain ⟨E, hEcomp, hEcross⟩ :=
    IsConnected.exists_annular_component_crossing_smaller hconn hcompact w hra hab hbR hcross
  obtain ⟨x, hx, hxE⟩ := hEcomp
  have hxFann : x ∈ F ∩ annulus w r R := ⟨(hclsub hx.1).1, hx.2⟩
  let D := connectedComponentIn (F ∩ annulus w r R) x
  have hED : E ⊆ D := by
    rw [← hxE]
    exact connectedComponentIn_mono x (fun _ hz => ⟨(hclsub hz.1).1, hz.2⟩)
  have hxC : x ∈ C := by
    obtain ⟨y, hy, hyC⟩ := hC.1
    rw [← hyC, connectedComponentIn_eq_closure_inter_of_isClosed hF hy]
    exact ⟨by simpa only [hyC] using hx.1, hx.2.1⟩
  have hDC : D ⊆ C := by
    obtain ⟨y, hy, hyC⟩ := hC.1
    rw [← hyC]
    apply connectedComponentIn_mono_of_mem
      (show F ∩ annulus w r R ⊆ F ∩ ball w R from fun _ hz => ⟨hz.1, hz.2.1⟩) hxFann
    exact hyC ▸ hxC
  have hDcross : CrossesAnnulus D w a b := by
    obtain ⟨⟨u, hu, hua⟩, ⟨v, hv, hvb⟩⟩ := hEcross
    exact ⟨⟨u, closure_mono hED hu, hua⟩, ⟨v, closure_mono hED hv, hvb⟩⟩
  exact ⟨D, ⟨x, hxFann, rfl⟩, hDC, hDcross⟩

/-- The number of ball crossings is bounded by the number of components in
the open annulus crossing the smaller concentric annulus. -/
theorem encard_ball_crossings_le_smaller_annular_crossings
    {F : Set ℂ} (hF : IsClosed F) (w : ℂ) {r a b R : ℝ}
    (hra : r < a) (hab : a < b) (hbR : b < R) :
    (crossingComponents (F ∩ ball w R) w r R).encard ≤
      (crossingComponents (F ∩ annulus w r R) w a b).encard := by
  classical
  let S := crossingComponents (F ∩ ball w R) w r R
  let T := crossingComponents (F ∩ annulus w r R) w a b
  have hex : ∀ C ∈ S, ∃ D ∈ T, D ⊆ C := by
    intro C hC
    obtain ⟨D, hD, hDC, hcross⟩ :=
      closed_ball_crossing_contains_smaller_annular_crossing hF w hra hab hbR hC
    exact ⟨D, ⟨hD, hcross⟩, hDC⟩
  let pick : Set ℂ → Set ℂ := fun C => if hC : C ∈ S then
    Classical.choose (hex C hC) else ∅
  have hpick : ∀ C ∈ S, pick C ∈ T ∧ pick C ⊆ C := by
    intro C hC
    simpa [pick, hC] using Classical.choose_spec (hex C hC)
  apply Set.encard_le_encard_of_injOn (fun C hC => (hpick C hC).1)
  intro C hC D hD heq
  by_contra hne
  have hdisj := pairwiseDisjoint_connectedComponentsIn (F ∩ ball w R) hC.1 hD.1 hne
  obtain ⟨x, hx, hxD⟩ := (hpick C hC).1.1
  have hxpick : x ∈ pick C := by
    rw [← hxD]
    exact mem_connectedComponentIn hx
  exact Set.disjoint_left.mp hdisj ((hpick C hC).2 hxpick) ((hpick D hD).2 (heq ▸ hxpick))

end HarmonicBalls
