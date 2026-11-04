import HarmonicBalls.Proofs.Sec3.ConservationOfMass
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Connected.LocallyConnected

/-! # Subharmonicity after componentwise truncation

A nonnegative subharmonic function can be restricted to an open set on which
it is subharmonic, provided it vanishes on the new interior boundary. This is
the truncation step in the proof of Lemma 6.8.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Filter Topology Set

/-- Truncating a continuous function across a zero boundary preserves continuity. -/
theorem continuousOn_indicator_of_zero_frontier {U Λ : Set ℂ} {u : ℂ → ℝ}
    (hcont : ContinuousOn u U) (hfront : ∀ x ∈ U ∩ frontier Λ, u x = 0) :
    ContinuousOn (Λ.indicator u) U := by
  classical
  have h := ContinuousOn.piecewise (s := U) (t := Λ) (f := u) (g := 0)
    (fun x hx => hfront x hx) (hcont.mono inter_subset_left)
    (continuousOn_const : ContinuousOn (fun _ : ℂ => (0 : ℝ)) (U ∩ closure Λᶜ))
  convert h using 1
  ext x
  by_cases hx : x ∈ Λ <;> simp [Set.piecewise, hx]

/-- A continuous, nonnegative function which is subharmonic on an open subset
remains subharmonic after extension by zero across a vanishing boundary. -/
theorem isSubharmonicOn_indicator_of_zero_frontier {U Λ : Set ℂ} {u : ℂ → ℝ}
    (hU : IsOpen U) (hΛ : IsOpen Λ)
    (hcont : ContinuousOn u U) (hnonneg : ∀ x ∈ U, 0 ≤ u x)
    (hfront : ∀ x ∈ U ∩ frontier Λ, u x = 0)
    (hsub : IsSubharmonicOn Λ u) : IsSubharmonicOn U (Λ.indicator u) := by
  classical
  let v := Λ.indicator u
  have hvc : ContinuousOn v U := continuousOn_indicator_of_zero_frontier hcont hfront
  have hv0 : ∀ x ∈ U, 0 ≤ v x := by
    intro x hx
    by_cases h : x ∈ Λ
    · simpa [v, h] using hnonneg x hx
    · simp [v, h]
  have hvs : IsSubharmonicOn Λ v := hsub.congr (fun x hx => by simp [v, hx])
  have hci : ∀ {x : ℂ} {r : ℝ}, 0 < r → closedBall x r ⊆ U → CircleIntegrable v x r :=
    fun hr hsubU => (hvc.mono (sphere_subset_closedBall.trans hsubU)).circleIntegrable hr.le
  have hloc : ∀ x ∈ U, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable (-v) x r ∧ Real.circleAverage (-v) x r ≤ (-v) x := by
    intro x hx
    by_cases hxΛ : x ∈ Λ
    · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hΛ x hxΛ
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      exact hvs.2 x hxΛ r hr.1 ((closedBall_subset_ball hr.2).trans hρsub)
    · obtain ⟨ρ, hρ, hρsub⟩ := Metric.isOpen_iff.1 hU x hx
      refine ⟨ρ, hρ, fun r hr => ?_⟩
      have hsubU : closedBall x r ⊆ U := (closedBall_subset_ball hr.2).trans hρsub
      have hvi := hci hr.1 hsubU
      refine ⟨hvi.neg, ?_⟩
      have havg := Real.circleAverage_mono
        (continuousOn_const.circleIntegrable' (f := fun _ : ℂ => (0 : ℝ))) hvi
        (fun y hy => hv0 y (hsubU (sphere_subset_closedBall (by rwa [abs_of_pos hr.1] at hy))))
      rw [Real.circleAverage_const] at havg
      rw [circleAverage_neg_fun, Pi.neg_apply]
      have hvx : v x = 0 := by simp [v, hxΛ]
      rw [hvx]
      linarith
  have hlsc : LowerSemicontinuousOn (-v) U := hvc.neg.lowerSemicontinuousOn
  exact ⟨hlsc, fun x hx r hr hsubU =>
    ⟨(hci hr hsubU).neg, circleAverage_le_of_localSuperMean hlsc hloc hr hsubU (hci hr hsubU).neg⟩⟩

/-- The zero extension also has nonnegative distributional Laplacian. -/
theorem laplacianGE_indicator_of_zero_frontier {U Λ : Set ℂ} {u : ℂ → ℝ}
    (hU : IsOpen U) (hΛ : IsOpen Λ)
    (hcont : ContinuousOn u U) (hnonneg : ∀ x ∈ U, 0 ≤ u x)
    (hfront : ∀ x ∈ U ∩ frontier Λ, u x = 0)
    (hsub : IsSubharmonicOn Λ u) : LaplacianGE (Λ.indicator u) 0 U := by
  have hc := continuousOn_indicator_of_zero_frontier hcont hfront
  have hs := isSubharmonicOn_indicator_of_zero_frontier hU hΛ hcont hnonneg hfront hsub
  exact LaplacianGE.of_laplacianLE_neg
    (laplacianLEOfSuperharmonicStep_holds U _ hU hc.neg hs)

/-- A union of connected components of an open planar set is open. -/
theorem isOpen_of_union_components {G Λ : Set ℂ} (hG : IsOpen G) (hΛG : Λ ⊆ G)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn G x ⊆ Λ) : IsOpen Λ := by
  have heq : Λ = ⋃ x ∈ Λ, connectedComponentIn G x := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion₂.mpr ⟨x, hx, mem_connectedComponentIn (hΛG hx)⟩
    · intro hx
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
      exact hcomp y hy hxy
  rw [heq]
  exact isOpen_iUnion fun x => isOpen_iUnion fun _ => hG.connectedComponentIn

/-- The frontier of a union of components of an open planar set misses the
open set itself. -/
theorem frontier_union_components_disjoint {G Λ : Set ℂ} (hG : IsOpen G) (hΛG : Λ ⊆ G)
    (hcomp : ∀ x ∈ Λ, connectedComponentIn G x ⊆ Λ) : Disjoint (frontier Λ) G := by
  apply disjoint_left.mpr
  intro x hxfront hxG
  have hxC : x ∈ connectedComponentIn G x := mem_connectedComponentIn hxG
  have hopen : IsOpen (connectedComponentIn G x) := hG.connectedComponentIn
  obtain ⟨y, hyC, hyΛ⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hxfront)
    (connectedComponentIn G x) (hopen.mem_nhds hxC)
  have hxCy : x ∈ connectedComponentIn G y := by
    rw [← connectedComponentIn_eq hyC]
    exact hxC
  have hxΛ : x ∈ Λ := hcomp y hyΛ hxCy
  have hΛopen := isOpen_of_union_components hG hΛG hcomp
  exact (disjoint_left.mp disjoint_interior_frontier) (by rwa [hΛopen.interior_eq]) hxfront

end HarmonicBalls.Section6
