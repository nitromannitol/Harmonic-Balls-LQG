import HarmonicBalls.Proofs.Sec6.BrownianAvoidance
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Integrated Brownian avoidance probabilities -/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess
open scoped ENNReal Topology

/-- On any finite measure of starting points in the domain, instant hitting of
the union forces integrated compact avoidance probabilities to vanish. -/
theorem tendsto_lintegral_avoidance_zero {U : Set ℂ} (hU : IsOpen U)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hx : ∀ᵐ x ∂ν, x ∈ U)
    (hhit : ∀ᵐ x ∂ν, ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0) :
    Tendsto (fun n => ∫⁻ x, planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (K n)ᶜ ω} ∂ν)
      atTop (𝓝 0) := by
  have hlim : ∀ᵐ x ∂ν, Tendsto (fun n => planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (K n)ᶜ ω}) atTop (𝓝 0) := by
    filter_upwards [hx, hhit] with x hx hhit
    exact tendsto_avoidance_probability_zero_of_instant_hit hU K hK hmono hx hhit
  have h := tendsto_lintegral_of_dominated_convergence (μ := ν) (f := fun _ => 0)
    (fun _ => 1)
    (fun n => measurable_avoidance_probability hU (hK n))
    (fun n => Filter.Eventually.of_forall fun x => by
      calc
        planarBrownianMotion x _ ≤ planarBrownianMotion x Set.univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ)
    (by simp) hlim
  simpa only [lintegral_zero] using h

/-- A positive uniform lower bound on integrated avoidance is incompatible
with instant hitting at almost every starting point. -/
theorem not_uniform_lintegral_avoidance_lower_bound {U : Set ℂ} (hU : IsOpen U)
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n)) (hmono : Monotone K)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hx : ∀ᵐ x ∂ν, x ∈ U)
    (hhit : ∀ᵐ x ∂ν, ∀ᵐ ω ∂(planarBrownianMotion x),
      ContinuousPath.exitTime (⋃ n, K n)ᶜ ω = 0)
    {d : ℝ≥0∞} (hd : 0 < d) :
    ¬ ∀ n, d ≤ ∫⁻ x, planarBrownianMotion x
      {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime (K n)ᶜ ω} ∂ν := by
  intro hlower
  have hlim := tendsto_lintegral_avoidance_zero hU K hK hmono ν hx hhit
  have hd0 : d ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hlower)
  exact (not_le_of_gt hd) hd0

/-- Fine support rules out uniformly positive integrated avoidance for every
compact set avoiding a dyadically small sequence of exceptions. -/
theorem not_uniform_avoidance_of_dyadic_exceptions
    {U A : Set ℂ} (hU : IsOpen U) (μ ν : Measure ℂ) [IsFiniteMeasure ν]
    (hA : MeasurableSet A) (hAfin : μ A ≠ ∞) (hx : ∀ᵐ x ∂ν, x ∈ U)
    (hfull : ∀ E : Set ℂ, MeasurableSet E → μ (A \ E) = 0 →
      ∀ᵐ x ∂ν, ∀ᵐ ω ∂(planarBrownianMotion x), ContinuousPath.exitTime Eᶜ ω = 0)
    (Y : ℕ → Set ℂ) (hY : ∀ n, MeasurableSet (Y n))
    (hsmall : ∀ n, μ (Y n) ≤ (2⁻¹ : ℝ≥0∞) ^ n * μ A)
    {d : ℝ≥0∞} (hd : 0 < d) :
    ¬ ∀ n (K : Set ℂ), IsCompact K → K ⊆ A \ Y n →
      d ≤ ∫⁻ x, planarBrownianMotion x
        {ω | ContinuousPath.exitTime U ω ≤ ContinuousPath.exitTime Kᶜ ω} ∂ν := by
  intro hlower
  obtain ⟨K, L, hK, hsub, hL, hmono, hLK, hmass⟩ :=
    compact_full_mass_of_dyadic_exceptions hA hAfin Y hY hsmall
  have hhit := hfull (⋃ n, L n) (MeasurableSet.iUnion fun n => (hL n).isClosed.measurableSet) hmass
  apply not_uniform_lintegral_avoidance_lower_bound hU L hL hmono ν hx hhit hd
  intro n
  apply (hlower n (K n) (hK n) (hsub n)).trans
  apply lintegral_mono
  intro x
  apply measure_mono
  intro ω hω
  exact hω.trans (ContinuousPath.exitTime_mono (compl_subset_compl.mpr (hLK n)) ω)

end HarmonicBalls.Section6
