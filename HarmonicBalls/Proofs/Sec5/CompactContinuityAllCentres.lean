import HarmonicBalls.Steps.Sec5.CompactContinuity

/-! # Compact right continuity for all unit-disc centres -/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter Topology
open scoped Pointwise
universe u

/-- Compact right continuity for every centre in the unit disc. -/
def ClusterCompactRightContinuityAllCentresStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t' ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z t') ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε


/-- Proposition 7.2 gives compact right continuity for all centres. -/
theorem clusterCompactRightContinuityAllCentres_of_steps (h33 : ClusterMonotoneStmt.{u})
    (h72 : ClusterTimeContinuityStmt.{u}) : ClusterCompactRightContinuityAllCentresStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  let β : ℝ := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1
  have hβrange : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < β := by dsimp [β]; linarith
  have hβ : 0 < β := by
    have hs : (0 : ℝ) ≤ (2 + γ) ^ 2 / 2 := by positivity
    have hm := le_max_left ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    linarith
  obtain ⟨C, hCpos, h72event⟩ := h72 γ α₀ hγ hγ2 hα β hβrange
  filter_upwards [h72event Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω htime hmono
  intro z hz t ht hcompact ε hε
  obtain ⟨r, hr, hsmall⟩ := exists_pos_of_eventually_nhdsGT (htime t ht z hz hcompact)
  have hexp : 0 < (1 : ℝ) / (4 * β) := by positivity
  obtain ⟨s, hs, hpow⟩ := exists_pos_forall_rpow_le hexp (div_pos hε (mul_pos (by norm_num : (0 : ℝ) < 2) hCpos))
  let δ := min r s / 2
  have hδ : 0 < δ := half_pos (lt_min hr hs)
  have hδr : δ < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
  have hδs : δ < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
  have hp := hpow δ hδ hδs
  have hrad : C * δ ^ (1 / (4 * β)) ≤ ε := by
    have h := mul_le_mul_of_nonneg_left hp hCpos.le
    have hcancel : C * (ε / (2 * C)) = ε / 2 := by field_simp
    rw [hcancel] at h
    linarith
  refine ⟨δ, hδ, fun t' ht' => ?_⟩
  have hsub : cluster (μ ω) 1 z t' ⊆ cluster (μ ω) 1 z (t + δ) :=
    hmono t' (t + δ) 1 (lt_of_lt_of_le ht ht'.1) ht'.2 (by norm_num) z hz
  exact (closure_mono hsub).trans ((hsmall δ hδ hδr).trans
    (add_subset_add Subset.rfl (ball_subset_ball hrad)))


end HarmonicBalls
