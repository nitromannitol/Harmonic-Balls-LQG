import HarmonicBalls.Proofs.Sec7.PositiveLocalStopping
import HarmonicBalls.Proofs.Sec5.LocalCompactFamilyRepresentative

/-! # A field-local family up to a positive time

The local representative agrees simultaneously at all centres in the half-disc
and all positive times up to a field-local stopping time. The proposed LQG
measure locality input and the existing regularized family remain explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- A positive field-local time and a simultaneous field-local representative
for every regularized family member at or before that time. -/
theorem exists_positive_fieldLocal_time_and_family_before
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ τ : Ω → Ioi (0 : ℝ), ∃ F : Ω → (ℂ × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] τ ∧
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] F ∧
      ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : Ioi (0 : ℝ),
        (t : ℝ) ≤ τ ω → closure (Λ ω z t) ⊆ ball 0 1 ∧ F ω (z, t) = Λ ω z t := by
  obtain ⟨τ, G, hτ, _, hstop⟩ := exists_positive_fieldLocal_time_and_family
    hI2 h71 hγ hγ2 hα hGFF hμ hloc hΛ
  obtain ⟨F, hF, hFeq⟩ := exists_local_lqg_bounded_compact_regularizedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc (U := ball (0 : ℂ) 1) isOpen_ball isBounded_ball hΛ
  refine ⟨τ, F, hτ, hF, ?_⟩
  filter_upwards [hstop, hFeq, hΛ] with ω hstopω hFω hfamily z hz t ht
  have hcl : closure (Λ ω z t) ⊆ ball 0 1 :=
    (closure_mono ((hfamily z).1.monotoneOn t.property (τ ω).property ht)).trans
      (hstopω ⟨z, hz⟩).1
  exact ⟨hcl, hFω z t hcl⟩

end HarmonicBalls
