import HarmonicBalls.Defs.LQGGraphDistance
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Topology.Homotopy.Affine

/-!
# Finiteness of Liouville graph distance

We acknowledge Leonardo Bonanno's contributions to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- A locally finite measure with no atoms admits arbitrarily small-mass balls. -/
theorem exists_ball_measure_le_of_singleton (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ x, μ {x} = 0) {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    ∃ r : ℝ, 0 < r ∧ μ (Metric.ball x r) ≤ ENNReal.ofReal ε := by
  have h : μ ({x} : Set ℂ) < ENNReal.ofReal ε := by
    rw [hμ x]
    exact ENNReal.ofReal_pos.mpr hε
  obtain ⟨U, hU, hUopen, hUm⟩ := isCompact_singleton.exists_isOpen_lt_of_lt _ h
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hUopen x (hU (by simp))
  exact ⟨r, hr, (measure_mono hrU).trans hUm.le⟩

/-- Every pair of points is joined by a path with a finite small-mass ball cover. -/
theorem exists_isLiouvilleGraphCover (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ x, μ {x} = 0) {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    ∃ n, IsLiouvilleGraphCover μ ε z w n := by
  classical
  choose r hr hrμ using fun x : ℂ => exists_ball_measure_le_of_singleton μ hμ hε x
  let p : Path z w := Path.segment z w
  have hc : IsCompact (Set.range p) := isCompact_range p.continuous
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover (fun x : ℂ => Metric.ball x (r x))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨x, Metric.mem_ball_self (hr x)⟩)
  let e : Fin s.card ≃ s := by
    simpa only [Fintype.card_coe] using (Fintype.equivFin s).symm
  refine ⟨s.card, (fun i => ((e i : s).val, r (e i : s).val)), ?_, p, ?_⟩
  · intro i
    exact ⟨hr _, hrμ _⟩
  · intro t
    have ht := hs (Set.mem_range_self t)
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, hxt⟩ := ht
    exact ⟨e.symm ⟨x, hx⟩, by simpa using hxt⟩

/-- Positive mass thresholds give finite Liouville graph distance. -/
theorem liouvilleGraphDistance_ne_top (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    (hμ : ∀ x, μ {x} = 0) {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    liouvilleGraphDistance μ ε z w ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_isLiouvilleGraphCover μ hμ hε z w
  exact ne_top_of_le_ne_top (by simp) (liouvilleGraphDistance_le hn)


end HarmonicBalls
