import HarmonicBalls.Proofs.Sec5.PuncturedDiscContact
import HarmonicBalls.Steps.Sec5.ClusterBounds

/-! # Small-time comparison at a puncture

The unit-disc small-time bound and the punctured-disc boundary contact result
show that admissibility prevents the two clusters from agreeing at small times.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- The small-time incompatibility holds with polynomially high probability,
with the same qualitative rate as Proposition 7.1. -/
theorem polyHighProb_small_time_punctured_disc_ne_of_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T,
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t ∈
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t →
      cluster (μ ω) 1 0 t ≠ clusterOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t}) := by
  have hsmall := h71 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 / 2) (by norm_num)
  apply hsmall.mono
  intro T ω hω t ht hv heq
  have ha : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by norm_num [mem_ball_zero_iff]
  have hz : (0 : ℂ) ∈ ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)} := by norm_num [mem_ball_zero_iff]
  have hbound := hω t ht 0 (by norm_num : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2))
  have hcl : closure (cluster (μ ω) 1 0 t) ⊆ ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)} := by
    intro x hx
    have hxsmall := hbound hx
    have hnorm : ‖x‖ < (1 / 4 : ℝ) := by
      norm_num [mem_ball_zero_iff] at hxsmall ⊢
      exact hxsmall
    refine ⟨mem_ball_zero_iff.mpr (by linarith), ?_⟩
    intro hxa
    have hxa' : x = (1 / 2 : ℂ) := by simpa using hxa
    subst x
    norm_num at hnorm
  exact (not_admissible_punctured_disc_of_compact_compatibility_proved ha hz ht.1 hcl
    (congrArg closure heq)) hv

/-- Assuming the numbered small-time upper bound, almost surely the unit-disc
cluster and the punctured-disc cluster differ throughout a positive interval
whenever the punctured-disc least supersolution is admissible. -/
theorem ae_small_time_punctured_disc_ne_of_admissible
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧ ∀ t ∈ Ioc (0 : ℝ) T,
      leastSupersolutionOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t ∈
        supersolutionsOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t →
      cluster (μ ω) 1 0 t ≠ clusterOn (μ ω) (ball (0 : ℂ) 1 \ {(1 / 2 : ℂ)}) 0 t := by
  have h := polyHighProb_small_time_punctured_disc_ne_of_admissible h71 hγ hγ2 hα hGFF hμ
  filter_upwards [h.ae_eventually_dyadic] with ω hω
  obtain ⟨n, hn⟩ := hω.exists
  exact ⟨(2 : ℝ)⁻¹ ^ n, by positivity, hn⟩

end HarmonicBalls
