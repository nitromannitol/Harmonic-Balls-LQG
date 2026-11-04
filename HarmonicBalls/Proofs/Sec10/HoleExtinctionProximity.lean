import HarmonicBalls.Proofs.Sec10.HoleExtinctionTotalMass

/-! # Spatial approach to an extinguishing hole

A lower volume-growth bound turns the total remaining mass estimate into a
quantitative assertion that the cluster approaches every interior ball. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- If a ball inside `U` has more mass than the part of `U` outside the
closure of `C`, then the ball meets `C`. -/
theorem ball_inter_nonempty_of_remaining_mass_lt
    (μ : Measure ℂ) {U C : Set ℂ} {p : ℂ} {r : ℝ}
    (hball : ball p r ⊆ U) (hmass : μ (U \ closure C) < μ (ball p r)) :
    (ball p r ∩ C).Nonempty := by
  by_contra hnone
  have hC : C ⊆ (ball p r)ᶜ := by
    intro x hx hxball
    exact hnone ⟨x, hxball, hx⟩
  have hcl : closure C ⊆ (ball p r)ᶜ := closure_minimal hC isOpen_ball.isClosed_compl
  have hsub : ball p r ⊆ U \ closure C := by
    intro x hx
    exact ⟨hball hx, fun h => hcl h hx⟩
  exact (not_le_of_gt hmass) (measure_mono hsub)

universe u

/-- Under I2 and 8.2, if a bounded hole's lifetime endpoint is compactly
contained, then at time `s` the cluster meets every ball of radius `r` in the
original hole as soon as `L - s < r ^ βm`. The exponent is deterministic and
the event is simultaneous in all poles, holes and admissible radii. -/
theorem ae_cluster_approaches_hole_before_extinction
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ βm : ℝ, ∀ᵐ ω ∂P, 0 < βm ∧ ∃ r₀ : ℝ, 0 < r₀ ∧
      ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s → s < L →
          ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (∀ s : ℝ, L < s →
          ¬ ∃ V ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z s))ᶜ, V ⊆ U) ∧
        (closure (cluster (μ ω) 1 z L) ⊆ ball 0 1 →
          ∀ p : ℂ, ∀ r : ℝ, 0 < r → r < r₀ → ball p r ⊆ U →
          ∀ s : ℝ, t ≤ s → s < L → L - s < r ^ βm →
          (ball p r ∩ cluster (μ ω) 1 z s).Nonempty) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  refine ⟨βm, ?_⟩
  filter_upwards [hV, ae_cluster_hole_remaining_mass_le_lifetime hI2 h82
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hV hlife
  obtain ⟨r₀, hr₀, hvol⟩ := (hV.2 1 zero_lt_one).2.2
  refine ⟨(hV.2 1 zero_lt_one).1, r₀, hr₀, ?_⟩
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter, hmass⟩ := hlife t ht z hz hcl U hU hUb
  refine ⟨L, htL, hbefore, hafter, ?_⟩
  intro hclL p r hr hrr hball s hts hsL hnear
  have hpU : p ∈ U := hball (mem_ball_self hr)
  have hcldisc : closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 1 :=
    hcl.trans ball_subset_closedBall
  have hp : p ∈ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure hcldisc hU hUb hpU
  apply ball_inter_nonempty_of_remaining_mass_lt (μ ω) hball
  calc
    μ ω (U \ closure (cluster (μ ω) 1 z s)) ≤ ENNReal.ofReal (L - s) :=
      (hmass hclL s hts hsL).1
    _ < ENNReal.ofReal (r ^ βm) :=
      (ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hr βm)).mpr hnear
    _ ≤ μ ω (ball p r) := (hvol r hr hrr p hp).1

end HarmonicBalls
