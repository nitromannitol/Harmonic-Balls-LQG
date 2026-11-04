import HarmonicBalls.Proofs.Sec10.UniformCrossingComparison
import HarmonicBalls.Proofs.Sec6.HarnackType

/-! # Prevalence of displaced crossing bounds -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped ENNReal

universe u

/-- Very good annuli give prevalent displaced-ball crossing bounds with the
crossing parameter chosen before the logarithmic singularity parameter. -/
theorem prevalent_displaced_crossing_events
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h69 : OdometerHarmonicMeasureBoundStmt.{u})
    (h66 : ManyVeryGoodAnnuliStmt.{u}) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∃ α : ℝ, 0 < α ∧ ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∃ E : ℝ → ℂ → Set Ω,
      (∀ ω, ∀ ρ ∈ Ioo (0 : ℝ) 1, ∀ x₀ : ℂ, ω ∈ E ρ x₀ →
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 → ∀ w : ℂ, dist w x₀ < ρ / 6 →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
          ⌈1 / α⌉₊) ∧
      PolyHighProb P fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
        c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
          ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀}.ncard : ℝ)} := by
  obtain ⟨c, C₃, hc, hC₃, h66⟩ := h66
  have hlog8 : 0 < Real.log 8 := Real.log_pos (by norm_num)
  refine ⟨c / Real.log 8, div_pos hc hlog8, fun γ hγ hγ2 => ?_⟩
  set β : ℝ := (2 + γ) ^ 2 / 2 + 1
  have hβ : (2 + γ) ^ 2 / 2 < β := by dsimp [β]; linarith
  have hβ0 : 0 < β := by dsimp [β]; positivity
  obtain ⟨b, hb, N₁f, αf, hN₁f, hcross⟩ :=
    exists_ae_crossing_thresholds_independent_exponent hI2 h69 hβ0 hC₃
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, -, h66⟩ :=
    h66 γ hγ hγ2 β hβ b hb
  set N₀ : ℕ := max N₁ (N₁f a C₁m C₂p)
  have hN₀ : N₁f a C₁m C₂p ≤ N₀ := le_max_right _ _
  have hα := (hN₁f a ha C₁m C₂p h1m h2p).2 N₀ hN₀
  refine ⟨αf a N₀ C₁m, hα.1, fun α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ => ?_⟩
  have hG := hcross hγ hγ2 hα₀ hGFF hμ
  set G : Set Ω := {ω | ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
    ∀ ρ : ℝ, 0 < ρ → ∀ x₀ : ℂ, closedBall x₀ ρ ⊆ ball (0 : ℂ) 1 →
    ∀ w : ℂ, dist w x₀ < ρ / 6 →
    ∀ a ∈ Ioo (0 : ℝ) 1, ∀ C₁m C₁p C₂m C₂p : ℝ, 0 < C₁m → 0 < C₂p →
    ∀ N₀ : ℕ, N₁f a C₁m C₂p ≤ N₀ →
    annulusBallMassSize (μ ω) β ρ x₀ / (μ ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p) →
    annulusGreenPotentialSup (μ ω) x₀ (ρ / 4) (2 * ρ) / (μ ω) (annulus x₀ (ρ / 4) (2 * ρ)) ∈
      Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p) →
    VeryGoodCriterionThree (μ ω) ρ x₀ N₀ a b C₃ →
    (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ)).encard ≤
      ⌈1 / αf a N₀ C₁m⌉₊}
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := hG
  refine ⟨fun ρ x₀ => {ω | ω ∈ G ∧ IsVeryGoodAnnulus (μ ω) β ρ x₀ N₀ a b C₁m C₁p C₂m C₂p C₃},
    fun ω ρ hρ x₀ hω z hz t ht hball w hw => ?_, ?_⟩
  · obtain ⟨hv1, hv2, hv3⟩ := (isVeryGoodAnnulus_iff _ _ _ _ _ _ _ _ _ _ _ _).mp hω.2
    exact hω.1 z hz t ht ρ hρ.1 x₀ hball w hw a ha C₁m C₁p C₂m C₂p h1m h2p N₀ hN₀ hv1 hv2 hv3
  · refine ((h66 N₀ (le_max_left _ _) α₀ hα₀ Ω P hC hcirc μ hGFF hμ).inter_ae hGae).mono
      fun ε ω hω x₀ hx₀ => ?_
    have hcount := hω.1 x₀ hx₀
    rw [div_log_eight_mul_log]
    refine hcount.trans_eq ?_
    congr 2
    ext ρ
    exact ⟨fun h => ⟨h.1, h.2.1, hω.2, h.2.2⟩, fun h => ⟨h.1, h.2.1, h.2.2.2⟩⟩

end HarmonicBalls
