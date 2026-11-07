import HarmonicBalls.Defs.LQGGraphDistance
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Homotopy.Affine

/-!
# Finiteness of Liouville graph distance

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- A nonatomic locally finite measure assigns arbitrarily small mass to some ball
centered at any given point. -/
theorem exists_small_mass_ball (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    [NullSingletonClass μ] (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ μ (Metric.ball x r) ≤ ENNReal.ofReal ε := by
  have h : μ ({x} : Set ℂ) < ENNReal.ofReal ε := by
    simpa using ENNReal.ofReal_pos.mpr hε
  obtain ⟨U, hU, hUopen, hmass⟩ := Set.exists_isOpen_lt_of_lt {x} _ h
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUopen x (hU (by simp))
  exact ⟨r, hr, (measure_mono hrU).trans hmass.le⟩

/-- A finite family of small-mass balls covers the straight path between any two points. -/
theorem exists_liouvilleGraphCover (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    [NullSingletonClass μ] {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    ∃ n : ℕ, IsLiouvilleGraphCover μ ε z w n := by
  classical
  let p : Path z w := Path.segment z w
  choose r hr hmass using fun x : ℂ => exists_small_mass_ball μ x hε
  have hc : IsCompact (Set.range p) := isCompact_range p.continuous
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun x : ℂ => Metric.ball x (r x))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hr x)⟩)
  let e := s.equivFin.symm
  refine ⟨s.card, fun i => ((e i).1, r (e i).1), ?_, p, ?_⟩
  · intro i
    exact ⟨hr _, hmass _⟩
  · intro t
    have ht := hs (Set.mem_range_self t)
    obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.mp ht
    exact ⟨s.equivFin ⟨x, hx⟩, by simpa [e] using hxt⟩

/-- Positive mass thresholds give finite Liouville graph distance for nonatomic
locally finite measures. -/
theorem liouvilleGraphDistance_ne_top_of_nonatomic (μ : Measure ℂ)
    [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    liouvilleGraphDistance μ ε z w ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_liouvilleGraphCover μ hε z w
  exact ne_top_of_le_ne_top (by simp) (liouvilleGraphDistance_le hn)

#print axioms liouvilleGraphDistance_ne_top_of_nonatomic

end HarmonicBalls
