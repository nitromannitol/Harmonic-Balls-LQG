import HarmonicBalls.Proofs.Sec5.BoundaryJumpDiameter
import HarmonicBalls.Proofs.Sec5.BoundaryContinuityCompactness

/-! # Counting boundary-only right-continuity failures -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal MeasureTheory

/-- Failure of the right-continuity bound at tolerance `2 * d` yields a
point in every future closure separated by `d` from the present closure. -/
theorem exists_separated_future_point_of_not_uniform_right_continuity
    (C : ℝ → Set ℂ) (t d : ℝ) (ht : 0 < t) (hd : 0 < d)
    (hmono : ∀ a b, 0 < a → a ≤ b → C a ⊆ C b)
    (hbound : ∀ s, 0 < s → C s ⊆ ball (0 : ℂ) 1)
    (hfail : ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (C s) ⊆ C t + ball (0 : ℂ) (2 * d)) :
    ∃ x ∈ ⋂ n : ℕ, closure (C (t + dyadicScale n)),
      ball x d ⊆ (closure (C t))ᶜ := by
  by_contra hnot
  have hinter : (⋂ n : ℕ, closure (C (t + (2 : ℝ)⁻¹ ^ n))) ⊆
      thickening d (closure (C t)) := by
    intro x hx
    by_contra hxU
    apply hnot
    refine ⟨x, hx, ?_⟩
    intro y hy hycl
    apply hxU
    exact mem_thickening_iff.mpr ⟨y, hycl, by simpa [dist_comm] using (mem_ball.mp hy)⟩
  obtain ⟨δ, hδ, hsub⟩ := eventually_closure_subset_open_of_iInter_subset ht hmono hbound
    isOpen_thickening hinter
  apply hfail
  refine ⟨δ, hδ, ?_⟩
  intro s hs x hx
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.mp (hsub s hs hx)
  obtain ⟨a, ha, hya⟩ := Metric.mem_closure_iff.mp hy d hd
  refine ⟨a, ha, x - a, ?_, by abel⟩
  have hdist : dist x a < 2 * d := by
    have htri := dist_triangle x y a
    linarith
  simpa [mem_ball, dist_eq_norm] using hdist

universe u

/-- For Liouville clusters, before any horizon there are at most
`⌈2π / d⌉` times at which increment mass vanishes and the right-continuity
bound fails at tolerance `2 * d`. -/
theorem ae_encard_boundary_right_continuity_failures_le
    (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ z ∈ ball (0 : ℂ) 1, ∀ d : ℝ, 0 < d →
      {t : ℝ | 0 < t ∧ t < T ∧
        (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
          μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
            ENNReal.ofReal ε) ∧
        ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
          closure (cluster (μ ω) 1 z s) ⊆
            cluster (μ ω) 1 z t + ball (0 : ℂ) (2 * d)}.encard ≤ ⌈2 * Real.pi / d⌉₊ := by
  filter_upwards [ae_encard_separated_boundary_jumps_le hvolume h32 h33 h61
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hcount hmono
  intro T z hz d hd
  apply (Set.encard_mono (show {t : ℝ | 0 < t ∧ t < T ∧
      (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
        μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
          ENNReal.ofReal ε) ∧
      ¬ ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) (2 * d)} ⊆
      {t : ℝ | 0 < t ∧ t < T ∧
        (∀ ε : ℝ, 0 < ε → ∃ n : ℕ,
          μ ω (cluster (μ ω) 1 z (t + dyadicScale n) \ cluster (μ ω) 1 z t) ≤
            ENNReal.ofReal ε) ∧
        ∃ x ∈ ⋂ n : ℕ, closure (cluster (μ ω) 1 z (t + dyadicScale n)),
          ball x d ⊆ (closure (cluster (μ ω) 1 z t))ᶜ} from ?_)).trans (hcount T z hz d hd)
  intro t ht
  refine ⟨ht.1, ht.2.1, ht.2.2.1, ?_⟩
  exact exists_separated_future_point_of_not_uniform_right_continuity
    (fun s => cluster (μ ω) 1 z s) t d ht.1 hd
    (fun a b ha hab => hmono a b 1 ha hab zero_lt_one z hz)
    (fun _ _ => cluster_subset_ball) ht.2.2.2

end HarmonicBalls

