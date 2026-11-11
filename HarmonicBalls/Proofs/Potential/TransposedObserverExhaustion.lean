import HarmonicBalls.Proofs.Potential.FiniteSourceObservationIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Observer exhaustion for transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- Restriction to an increasing almost-everywhere covering sequence converges in L¹. -/
theorem integrable_indicator_exhaustion_l1 {α : Type*} [MeasurableSpace α]
    {m : Measure α} {f : α → ℝ} (hf : Integrable f m)
    (A : ℕ → Set α) (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A)
    (hcover : m (⋃ n, A n)ᶜ = 0) :
    (∀ n, Integrable ((A n).indicator f) m) ∧
    (∀ᵐ x ∂m, Tendsto (fun n => (A n).indicator f x) atTop (𝓝 (f x))) ∧
    Tendsto (fun n => ∫ x, ‖(A n).indicator f x - f x‖ ∂m) atTop (𝓝 0) := by
  have hi (n : ℕ) := hf.indicator (hA n)
  have hc : ∀ᵐ x ∂m, x ∈ ⋃ n, A n := by
    rw [ae_iff]
    exact hcover
  have hp : ∀ᵐ x ∂m, Tendsto (fun n => (A n).indicator f x) atTop (𝓝 (f x)) := by
    filter_upwards [hc] with x hx
    obtain ⟨N, hN⟩ := mem_iUnion.mp hx
    apply (tendsto_congr' ?_).2 tendsto_const_nhds
    filter_upwards [eventually_ge_atTop N] with n hn
    exact indicator_of_mem (hmono hn hN) _
  refine ⟨hi, hp, ?_⟩
  have ht := tendsto_integral_of_dominated_convergence (μ := m) (fun x => ‖f x‖)
    (fun n => ((hi n).sub hf).norm.aestronglyMeasurable) hf.norm
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ A n <;> simp [indicator_of_mem, indicator_of_notMem, hx])
    (hp.mono fun x hx => by simpa using (hx.sub tendsto_const_nhds).norm)
  simpa using ht

/-- Observer restrictions of the literal transposed Green potential converge in L¹.
The source kernel is Bochner integrable at almost every observer. -/
theorem transposed_green_observer_exhaustion_l1
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) (A : ℕ → Set ℂ)
    (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A)
    (hcover : (μ.restrict V) (⋃ n, A n)ᶜ = 0) :
    (∀ᵐ x ∂μ.restrict V, Integrable (fun y => greenFunction V y x) ν) ∧
    Integrable (fun x => ∫ y, greenFunction V y x ∂ν) (μ.restrict V) ∧
    (∀ n, Integrable ((A n).indicator (fun x => ∫ y, greenFunction V y x ∂ν))
      (μ.restrict V)) ∧
    (∀ᵐ x ∂μ.restrict V, Tendsto
      (fun n => (A n).indicator (fun x => ∫ y, greenFunction V y x ∂ν) x)
      atTop (𝓝 (∫ y, greenFunction V y x ∂ν))) ∧
    Tendsto (fun n => ∫ x in V, ‖(A n).indicator
      (fun x => ∫ y, greenFunction V y x ∂ν) x -
      (∫ y, greenFunction V y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨hk, hf⟩ := finiteSource_transposedGreen_observation_integrability hup hV hVb hν
  exact ⟨hk, hf, integrable_indicator_exhaustion_l1 hf A hA hmono hcover⟩


end HarmonicBalls
