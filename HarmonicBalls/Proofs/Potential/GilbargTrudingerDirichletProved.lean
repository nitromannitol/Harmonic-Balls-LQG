import Mathlib
import HarmonicBalls.Proposed.GilbargTrudinger
import HarmonicBalls.Proofs.Potential.PerronBoundary

/-!
# Gilbarg–Trudinger, Theorem 2.14, in the plane

Source: D. Gilbarg and N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
2nd edition, revised third printing, Springer (2001), Theorem 2.14, p. 26, with the exterior-sphere
barrier (2.34), p. 27.

The Dirichlet problem for the Laplacian on a bounded plane domain satisfying the exterior sphere
condition at every boundary point is solvable for every continuous boundary datum.  The proof is the
Perron method of Section 2.8: the supremum of the subfunctions is harmonic (`harmonicOnNhd_perronFun`),
and the logarithmic barrier of an exterior disc (`exists_barrier`) gives the boundary values
(`perronFun_close`).

* `HarmonicBalls.gilbargTrudingerThm2_14_holds`: the statement `GilbargTrudingerThm2_14`, proved.
-/

namespace HarmonicBalls

open Metric Set Filter Topology

open Classical in
/-- **Gilbarg–Trudinger, Theorem 2.14**, for the Laplacian on `ℂ ≅ ℝ²`. -/
theorem gilbargTrudingerThm2_14_holds : GilbargTrudingerThm2_14 := by
  intro U hU _ hbdd hext φ hφ
  have hfrc : IsCompact (frontier U) :=
    hbdd.isCompact_closure.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨B, hB⟩ := hfrc.exists_bound_of_continuousOn hφ
  have hB' : ∀ z ∈ frontier U, |φ z| ≤ B := fun z hz => by
    simpa [Real.norm_eq_abs] using hB z hz
  have hm : ∀ z ∈ frontier U, -B ≤ φ z := fun z hz => (abs_le.mp (hB' z hz)).1
  have hM : ∀ z ∈ frontier U, φ z ≤ B := fun z hz => (abs_le.mp (hB' z hz)).2
  have hH := harmonicOnNhd_perronFun hU hbdd hm hM
  have hfr_not : ∀ z ∈ frontier U, z ∉ U := fun z hz => by
    rw [hU.frontier_eq] at hz
    exact hz.2
  set F : ℂ → ℝ := fun x => if x ∈ U then perronFun U φ x else φ x with hF
  have hFU : ∀ x ∈ U, F x = perronFun U φ x := fun x hx => by simp [hF, hx]
  have hFfr : ∀ x ∈ frontier U, F x = φ x := fun x hx => by simp [hF, hfr_not x hx]
  have hFev : ∀ x ∈ U, F =ᶠ[𝓝 x] perronFun U φ := fun x hx => by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hFU y hy
  refine ⟨F, ?_, ?_, hFfr⟩
  · intro x hx
    rw [closure_eq_self_union_frontier] at hx
    rcases hx with hxU | hxfr
    · exact (((hH x hxU).1.continuousAt).congr (hFev x hxU).symm).continuousWithinAt
    · obtain ⟨w, r, hr, hdist, hball⟩ := hext x hxfr
      obtain ⟨β, hβc, hβh, hβ0, hβξ, hβlow⟩ := exists_barrier hr hdist hball
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      obtain ⟨δ₁, hδ₁, h₁⟩ := perronFun_close hU hbdd hB' hxfr (hφ x hxfr) hβc hβh hβ0 hβξ hβlow hε
      obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.continuousWithinAt_iff.mp (hφ x hxfr) ε hε
      refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy hyd => ?_⟩
      rw [hFfr x hxfr]
      rw [closure_eq_self_union_frontier] at hy
      rcases hy with hyU | hyfr
      · rw [hFU y hyU, Real.dist_eq]
        exact h₁ y hyU (hyd.trans_le (min_le_left _ _))
      · rw [hFfr y hyfr]
        exact h₂ hyfr (hyd.trans_le (min_le_right _ _))
  · intro x hx
    exact (InnerProductSpace.harmonicAt_congr_nhds (hFev x hx)).mpr (hH x hx)

end HarmonicBalls
