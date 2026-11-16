import HarmonicBalls.FirstPass.Phase2.MetricPropernessCrossing

/-!
# Large-scale crossings for a logarithmic insertion

The normalized crossing estimate retains the scale factor and the circle
average needed to compare the metric with a logarithmic Weyl scaling.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

open LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS.L38 LQGMetric.GM.Tight

/-- Infinitely many annuli have the normalized lower crossing bound for the
whole-plane metric, simultaneously for all pairs crossing each annulus. -/
theorem ae_frequently_normalized_far_crossing {γ : ℝ} {D : DistC → ContMetric}
    (hD : IsWeakLQGMetric γ D (fun r => r ^ (xiGamma γ * Q γ)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) :
    ∃ s : ℝ, 0 < s ∧ ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ j : ℕ, m ≤ j ∧
      ∀ x y : ℂ, ‖x‖ ≤ 8 ^ j / 4 → 3 * 8 ^ j / 8 ≤ ‖y‖ →
        s * (8 ^ j : ℝ) ^ (xiGamma γ * Q γ) *
          Real.exp (xiGamma γ * circleAvg (h ω) (8 ^ j) 0) ≤ (D (h ω)).1 (x, y) := by
  obtain ⟨p, hp0, hp1, HA⟩ := ae_frequently_crossing LQGMetric.LM.lmLem3_1a
  obtain ⟨s, hs, Hev⟩ := exists_crossing_event hD (ε := ENNReal.ofReal (1 - p))
    (ENNReal.ofReal_pos.2 (by linarith))
  refine ⟨s, hs, ?_⟩
  have hwp := hh.1
  choose E hEm hEc hEae using fun ρ : {ρ : ℝ // 0 < ρ} => Hev P h hwp ρ.1 ρ.2
  have hEp : ∀ ρ, ENNReal.ofReal p ≤ P (E ρ) := fun ρ => by
    have h1 : (1 : ℝ≥0∞) ≤ P (E ρ) + P (E ρ)ᶜ := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono (union_compl_self (E ρ)).symm.subset).trans (measure_union_le _ _)
    have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add hp0.le (by linarith)]
      simp
    rw [← h2] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1
      (h1.trans (add_le_add le_rfl (hEc ρ).le))
  have hEall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ E ⟨8 ^ j, by positivity⟩ →
      ∀ u ∈ sphere (0 : ℂ) (8 ^ j / 4), ∀ v ∈ sphere (0 : ℂ) (3 * 8 ^ j / 8),
        ENNReal.ofReal (s * (8 ^ j : ℝ) ^ (xiGamma γ * Q γ) *
          Real.exp (xiGamma γ * circleAvg (h ω) (8 ^ j) 0)) ≤
          (D (h ω)).internal (annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j)) u v :=
    ae_all_iff.2 fun j => hEae ⟨8 ^ j, by positivity⟩
  filter_upwards [HA P h hh E hEm hEp,
    hD.length P h (isGFFPlusCont_of_wp hwp), hEall] with ω hfreq hlen hcross
  intro m
  obtain ⟨j, hj, hjE⟩ := hfreq m
  refine ⟨j, hj, fun x y hx hy => ?_⟩
  have hU : {w : ℂ | 8 ^ j / 4 ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ 3 * 8 ^ j / 8} ⊆
      (annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j) : Set ℂ) := fun w hw => by
    show 1 / 8 * 8 ^ j < ‖w - 0‖ ∧ ‖w - 0‖ < 1 / 2 * (8 : ℝ) ^ j
    constructor <;> linarith [hw.1, hw.2, show (0 : ℝ) < 8 ^ j by positivity]
  exact le_of_forall_internal_crossing (y := y) hlen (by linarith [show (0 : ℝ) < 8 ^ j by positivity]) hU
    (by simpa only [sub_zero] using hx) (by simpa only [sub_zero] using hy) (hcross j hjE)

end HarmonicBalls
