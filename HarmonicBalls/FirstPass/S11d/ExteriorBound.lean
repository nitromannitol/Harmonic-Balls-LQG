import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.FirstPass.S11d.Finite

/-!
# Proposition 11.9, finiteness of the exterior internal diameter

Deterministic input to the exterior bound of `prop:mass-diam-gen` (corrected paper, lines 3120-3125):
for a Euclidean length metric `D`, an open set `O`, and an open preconnected `A` with `closure A ⊆ O` and compact
`closure A`, the internal distance `D(·,·; O)` is finite on `closure A × closure A` and its supremum over `A` is finite.
Proof: every point `x ∈ closure A` has a point `y ∈ A` joined to `x` by a path in a ball `B(x,r) ⊆ O`
(`internalMetric_lt_top_of_joinedIn`); two triangle inequalities then bound `D(u,v;O)` by finite terms; the
continuous `ℝ≥0∞`-valued function `D(·,·;O)` attains its maximum on the compact `closure A × closure A`.
-/

namespace HarmonicBalls

open Set Filter Topology
open scoped ENNReal

/-- Finiteness on `closure A`: any two points of `closure A` have finite internal distance in `O`. -/
theorem internalMetric_lt_top_on_closure {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O A : Set ℂ} (hO : IsOpen O) (hA : IsOpen A) (hAc : IsPreconnected A)
    (hclO : closure A ⊆ O) {u v : ℂ} (hu : u ∈ closure A) (hv : v ∈ closure A) :
    internalMetric D O u v < ⊤ := by
  -- every point of `closure A` is joined inside `O` to a point of `A`, in both directions
  have hnear : ∀ x ∈ closure A, ∃ y ∈ A, internalMetric D O x y < ⊤ ∧ internalMetric D O y x < ⊤ := by
    intro x hx
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO x (hclO hx)
    obtain ⟨y, hyball, hyA⟩ := mem_closure_iff.mp hx (Metric.ball x r) Metric.isOpen_ball
      (Metric.mem_ball_self hr)
    have hpc : IsPathConnected (Metric.ball x r) :=
      (convex_ball x r).isPathConnected ⟨x, Metric.mem_ball_self hr⟩
    have hxy : JoinedIn (Metric.ball x r) x y := hpc.joinedIn x (Metric.mem_ball_self hr) y hyball
    have hyx : JoinedIn (Metric.ball x r) y x := hpc.joinedIn y hyball x (Metric.mem_ball_self hr)
    exact ⟨y, hyA, hD.internalMetric_lt_top_of_joinedIn hnonneg hO (hxy.mono hball),
      hD.internalMetric_lt_top_of_joinedIn hnonneg hO (hyx.mono hball)⟩
  obtain ⟨u', hu'A, hu'⟩ := hnear u hu
  obtain ⟨v', hv'A, hv'⟩ := hnear v hv
  have hfin : internalMetric D O u' v' < ⊤ :=
    internalMetric_lt_top_of_mem_preconnected hD hnonneg hO hA hAc (fun x hx => hclO (subset_closure hx))
      hu'A hv'A
  calc internalMetric D O u v
      ≤ internalMetric D O u v' + internalMetric D O v' v := hD.internalMetric_triangle O u v' v
    _ ≤ (internalMetric D O u u' + internalMetric D O u' v') + internalMetric D O v' v :=
        add_le_add (hD.internalMetric_triangle O u u' v') le_rfl
    _ < ⊤ := ENNReal.add_lt_top.mpr
        ⟨ENNReal.add_lt_top.mpr ⟨hu'.1, hfin⟩, hv'.2⟩

/-- The supremum of `D(·,·; O)` over `A` is finite when `closure A` is compact. -/
theorem iSup_internalMetric_lt_top {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O A : Set ℂ} (hO : IsOpen O) (hA : IsOpen A) (hAc : IsPreconnected A)
    (hclO : closure A ⊆ O) (hK : IsCompact (closure A)) :
    (⨆ u ∈ A, ⨆ v ∈ A, internalMetric D O u v) < ⊤ := by
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · subst hAe
    simp
  have hKne : (closure A ×ˢ closure A).Nonempty := (hAne.mono subset_closure).prod (hAne.mono subset_closure)
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric D O p.1 p.2) (closure A ×ˢ closure A) :=
    (hD.continuousOn_internalMetric_pair hnonneg hO).mono (prod_mono hclO hclO)
  obtain ⟨p0, hp0, hmax⟩ := (hK.prod hK).exists_isMaxOn hKne hcont
  have hbound : (⨆ u ∈ A, ⨆ v ∈ A, internalMetric D O u v) ≤ internalMetric D O p0.1 p0.2 := by
    refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
    have hmem : (u, v) ∈ closure A ×ˢ closure A := ⟨subset_closure hu, subset_closure hv⟩
    exact isMaxOn_iff.mp hmax (u, v) hmem
  exact lt_of_le_of_lt hbound
    (internalMetric_lt_top_on_closure hD hnonneg hO hA hAc hclO hp0.1 hp0.2)

end HarmonicBalls
