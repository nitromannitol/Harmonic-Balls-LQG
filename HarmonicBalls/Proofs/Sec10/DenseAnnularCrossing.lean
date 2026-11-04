import HarmonicBalls.Proofs.Sec10.IrreducibleAnnulus

/-!
# Dense connected subsets of annular crossings

A connected subset of the open annulus whose closure meets both boundary
circles is contained in an annular component crossing both circles.
-/

namespace HarmonicBalls

open Metric Set Topology

/-- A connected annular crossing is contained in a crossing component of any
larger set in the annulus. -/
theorem connected_annular_crossing_subset_component
    {K S : Set ℂ} (w : ℂ) (r R : ℝ)
    (hSK : S ⊆ K ∩ annulus w r R) (hS : IsConnected S)
    (hcross : CrossesAnnulus S w r R) :
    ∃ D ∈ crossingComponents (K ∩ annulus w r R) w r R, S ⊆ D := by
  obtain ⟨x, hx⟩ := hS.nonempty
  let D := connectedComponentIn (K ∩ annulus w r R) x
  have hSD : S ⊆ D := hS.isPreconnected.subset_connectedComponentIn hx hSK
  have hcrossD : CrossesAnnulus D w r R := by
    obtain ⟨⟨a, ha, har⟩, ⟨b, hb, hbR⟩⟩ := hcross
    exact ⟨⟨a, closure_mono hSD ha, har⟩, ⟨b, closure_mono hSD hb, hbR⟩⟩
  exact ⟨D, ⟨⟨x, hSK hx, rfl⟩, hcrossD⟩, hSD⟩

/-- A connected set in an annular slice whose closure contains a compact
crossing gives a component crossing the two original circles. -/
theorem dense_annular_crossing_subset_component
    {K M S : Set ℂ} (w : ℂ) (r R : ℝ)
    (hSK : S ⊆ K ∩ annulus w r R) (hS : IsConnected S)
    (hMcl : M ⊆ closure S)
    (hMr : (M ∩ sphere w r).Nonempty) (hMR : (M ∩ sphere w R).Nonempty) :
    ∃ D ∈ crossingComponents (K ∩ annulus w r R) w r R, M ⊆ closure D := by
  have hcross : CrossesAnnulus S w r R := by
    obtain ⟨a, haM, har⟩ := hMr
    obtain ⟨b, hbM, hbR⟩ := hMR
    exact ⟨⟨a, hMcl haM, har⟩, ⟨b, hMcl hbM, hbR⟩⟩
  obtain ⟨D, hD, hSD⟩ := connected_annular_crossing_subset_component w r R hSK hS hcross
  exact ⟨D, hD, hMcl.trans (closure_mono hSD)⟩

/-- An annular crossing contains a subcontinuum irreducible between the two
circles, confined to the closed annulus, and with dense open-annulus part. -/
theorem exists_minimal_closed_annulus_crossing
    {K : Set ℂ} (hKc : IsCompact K) (hK : IsConnected K)
    (w : ℂ) {r R : ℝ} (hrR : r < R)
    (hKball : K ⊆ closedBall w R) (hcross : CrossesAnnulus K w r R) :
    ∃ M : Set ℂ, M ⊆ K ∧ IsCompact M ∧ IsConnected M ∧
      M ⊆ closedBall w R \ ball w r ∧
      (M ∩ sphere w r).Nonempty ∧ (M ∩ sphere w R).Nonempty ∧
      closure (M ∩ annulus w r R) = M ∧
      ∀ N : Set ℂ, N ⊆ M → IsCompact N → IsConnected N →
        (N ∩ sphere w r).Nonempty → (N ∩ sphere w R).Nonempty → N = M := by
  obtain ⟨L, hLK, hLc, hL, hLann, hLA, hLB, _⟩ :=
    exists_irreducible_closed_annulus_crossing hKc hK w hrR hKball hcross
  obtain ⟨M, hML, hMc, hM, hMA, hMB, hmin⟩ :=
    exists_irreducible_subcontinuum_between_closed_sets hLc hL isClosed_sphere
      isClosed_sphere hLA hLB
  have hMann : M ⊆ closedBall w R \ ball w r := hML.trans hLann
  have hAB : Disjoint (sphere w r) (sphere w R) := by
    rw [Set.disjoint_left]
    intro x hx hy
    have hx' := mem_sphere.mp hx
    have hy' := mem_sphere.mp hy
    linarith
  have heq : M ∩ annulus w r R = M ∩ (sphere w r)ᶜ ∩ (sphere w R)ᶜ := by
    ext x
    simp only [mem_inter_iff, annulus, mem_sdiff, mem_ball, mem_closedBall,
      mem_compl_iff, mem_sphere]
    constructor
    · rintro ⟨hxM, hxR, hxr⟩
      exact ⟨⟨hxM, by linarith⟩, by linarith⟩
    · rintro ⟨⟨hxM, hxr⟩, hxR⟩
      have hx := hMann hxM
      have hlo : r ≤ dist x w := le_of_not_gt (fun h => hx.2 (mem_ball.mpr h))
      have hhi : dist x w ≤ R := mem_closedBall.mp hx.1
      exact ⟨hxM, lt_of_le_of_ne hhi hxR,
        not_le_of_gt (lt_of_le_of_ne hlo (Ne.symm hxr))⟩
  have hdense : closure (M ∩ annulus w r R) = M := by
    rw [heq]
    exact irreducible_both_compl_dense hMc hM isClosed_sphere isClosed_sphere
      hAB hMA hMB hmin
  exact ⟨M, hML.trans hLK, hMc, hM, hMann, hMA, hMB, hdense, hmin⟩

end HarmonicBalls
