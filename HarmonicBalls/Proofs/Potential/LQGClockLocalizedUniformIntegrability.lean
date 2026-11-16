import HarmonicBalls.Proofs.Potential.LQGClockExpectationLimit
import LatticeProb.Prob.UniformIntegrableDominated

/-! # Localized increment bounds for stopped Liouville clocks

A summable field-integral bound for localized envelopes of the stopped clock
increments gives quenched uniform integrability simultaneously for all smooth
bounded domains and all starting points in each domain. Envelopes may depend
on a ball containing the domain.
-/

namespace HarmonicBalls

open MeasureTheory MarkovProcess Filter Set
open scoped ENNReal

/-- Localized summable envelopes for the actual stopped dyadic clock increments
imply quenched uniform integrability on one field event for all admissible
starting points and domains. -/
theorem ae_uniformIntegrable_stopped_clockApprox_of_localized_increments
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (γ : ℝ)
    (hε : Ω → ℝ → ℂ → ℝ) (E : ℕ → Set Ω) (g : ℕ → ℕ → ℕ → Ω → ℝ)
    (hE : ∀ m, MeasurableSet (E m))
    (hcover : ∀ᵐ ω ∂ν, ∃ m, ω ∈ E m)
    (hg : ∀ m j k, AEStronglyMeasurable (g m j k) (ν.restrict (E m)))
    (hsum : ∀ m j, (∑' k, ∫⁻ ω, ‖g m j k ω‖ₑ ∂(ν.restrict (E m))) ≠ ∞)
    (hint : ∀ m ω, ω ∈ E m → ∀ D : Set ℂ, IsSmoothBoundedOpen D →
      ∀ x ∈ D, ∀ k : ℕ,
        Integrable (fun b => lqgClockApprox γ (hε ω) (dyadicScale k) b
          (ContinuousPath.exitTime D b).toNNReal) (planarBrownianMotion x))
    (hbound : ∀ m ω, ω ∈ E m → ∀ j : ℕ, ∀ D : Set ℂ, IsSmoothBoundedOpen D →
      D ⊆ Metric.ball 0 (j : ℝ) → ∀ x ∈ D, ∀ k : ℕ,
        (∫ b, ‖lqgClockApprox γ (hε ω) (dyadicScale (k + 1)) b
            (ContinuousPath.exitTime D b).toNNReal -
          lqgClockApprox γ (hε ω) (dyadicScale k) b
            (ContinuousPath.exitTime D b).toNNReal‖ ∂(planarBrownianMotion x)) ≤ ‖g m j k ω‖) :
    ∀ᵐ ω ∂ν, ∀ D : Set ℂ, IsSmoothBoundedOpen D → ∀ x ∈ D,
      UniformIntegrable (fun k : ℕ => fun b =>
        lqgClockApprox γ (hε ω) (dyadicScale k) b
          (ContinuousPath.exitTime D b).toNNReal) 1 (planarBrownianMotion x) := by
  have hfield : ∀ᵐ ω ∂ν, ∀ m, ω ∈ E m → ∀ j, Summable (fun k => ‖g m j k ω‖) := by
    apply ae_all_iff.mpr
    intro m
    apply (ae_restrict_iff' (hE m)).mp
    apply ae_all_iff.mpr
    intro j
    have hm : AEMeasurable (fun ω => ∑' k, ‖g m j k ω‖ₑ) (ν.restrict (E m)) :=
      AEMeasurable.tsum fun k => (hg m j k).enorm
    have hf : (∫⁻ ω, ∑' k, ‖g m j k ω‖ₑ ∂(ν.restrict (E m))) ≠ ∞ := by
      rw [lintegral_tsum (fun k => (hg m j k).enorm)]
      exact hsum m j
    filter_upwards [ae_lt_top' hm hf] with ω hω
    exact tsum_enorm_ne_top_iff_summable_norm.mp hω.ne
  filter_upwards [hcover, hfield] with ω hω hωsum
  obtain ⟨m, hm⟩ := hω
  intro D hD x hx
  obtain ⟨r, hr⟩ := hD.1.subset_ball (0 : ℂ)
  obtain ⟨j, hj⟩ := exists_nat_gt r
  have hDj : D ⊆ Metric.ball (0 : ℂ) (j : ℝ) :=
    hr.trans (Metric.ball_subset_ball hj.le)
  apply LatticeProb.Prob.uniformIntegrable_of_summable_integral_norm_sub
    (hint m ω hm D hD x hx)
  exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (hbound m ω hm j D hD hDj x hx) (hωsum m hm j)

end HarmonicBalls
