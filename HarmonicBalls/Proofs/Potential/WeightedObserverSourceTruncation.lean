import HarmonicBalls.Proofs.Potential.WeightedObservationStability
import HarmonicBalls.Proofs.Potential.TransposedObserverExhaustion

/-! # Joint source and observer truncation

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- Bounded signed source densities and an almost-everywhere observer exhaustion
converge jointly for the literal transposed Green potential, pointwise and in L¹. -/
theorem weighted_transposedGreen_joint_truncation
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (C : ℝ)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hbound : ∀ n y, ‖f n y‖ ≤ C) (hgbound : ∀ y, ‖g y‖ ≤ C)
    (hconv : ∀ᵐ y ∂ν, Tendsto (fun n => f n y) atTop (𝓝 (g y)))
    (A : ℕ → Set ℂ) (hA : ∀ n, MeasurableSet (A n)) (hmono : Monotone A)
    (hcover : (μ.restrict V) (⋃ n, A n)ᶜ = 0) :
    (∀ n, Integrable ((A n).indicator
      (fun x => ∫ y, f n y * greenFunction V y x ∂ν)) (μ.restrict V)) ∧
    Integrable (fun x => ∫ y, g y * greenFunction V y x ∂ν) (μ.restrict V) ∧
    (∀ᵐ x ∂μ.restrict V, Tendsto
      (fun n => (A n).indicator (fun x => ∫ y, f n y * greenFunction V y x ∂ν) x)
      atTop (𝓝 (∫ y, g y * greenFunction V y x ∂ν))) ∧
    Tendsto (fun n => ∫ x in V, ‖(A n).indicator
      (fun x => ∫ y, f n y * greenFunction V y x ∂ν) x -
      (∫ y, g y * greenFunction V y x ∂ν)‖ ∂μ) atTop (𝓝 0) := by
  obtain ⟨hi, hgprod, hp, hl⟩ :=
    weighted_transposedGreen_observation_stability hup hV hVb hν f g C hf hg hbound hgbound hconv
  let P : ℕ → ℂ → ℝ := fun n x => ∫ y, f n y * greenFunction V y x ∂ν
  let Q : ℂ → ℝ := fun x => ∫ y, g y * greenFunction V y x ∂ν
  have hPi (n : ℕ) : Integrable (P n) (μ.restrict V) := (hi n).integral_prod_right
  have hQi : Integrable Q (μ.restrict V) := hgprod.integral_prod_right
  have hAi (n : ℕ) : Integrable ((A n).indicator (P n)) (μ.restrict V) :=
    (hPi n).indicator (hA n)
  have hc : ∀ᵐ x ∂μ.restrict V, x ∈ ⋃ n, A n := by
    rw [ae_iff]
    exact hcover
  have hpoint : ∀ᵐ x ∂μ.restrict V, Tendsto
      (fun n => (A n).indicator (P n) x) atTop (𝓝 (Q x)) := by
    filter_upwards [hp, hc] with x hx hxc
    obtain ⟨N, hN⟩ := mem_iUnion.mp hxc
    apply (tendsto_congr' ?_).2 hx
    filter_upwards [eventually_ge_atTop N] with n hn
    exact indicator_of_mem (hmono hn hN) _
  obtain ⟨hQind, _, hQlim⟩ := integrable_indicator_exhaustion_l1 hQi A hA hmono hcover
  refine ⟨hAi, hQi, hpoint, ?_⟩
  have hsum : Tendsto (fun n => (∫ x, ‖P n x - Q x‖ ∂(μ.restrict V)) +
      ∫ x, ‖(A n).indicator Q x - Q x‖ ∂(μ.restrict V)) atTop (𝓝 0) := by
    simpa using hl.add hQlim
  apply squeeze_zero (fun n => integral_nonneg fun x => norm_nonneg _) _ hsum
  intro n
  have hadd : (∫ x, (‖P n x - Q x‖ + ‖(A n).indicator Q x - Q x‖) ∂(μ.restrict V)) =
      (∫ x, ‖P n x - Q x‖ ∂(μ.restrict V)) +
      ∫ x, ‖(A n).indicator Q x - Q x‖ ∂(μ.restrict V) :=
    integral_add ((hPi n).sub hQi).norm ((hQind n).sub hQi).norm
  rw [← hadd]
  apply integral_mono_ae ((hAi n).sub hQi).norm
    (((hPi n).sub hQi).norm.add ((hQind n).sub hQi).norm)
  filter_upwards [] with x
  change ‖(A n).indicator (P n) x - Q x‖ ≤
    ‖P n x - Q x‖ + ‖(A n).indicator Q x - Q x‖
  by_cases hx : x ∈ A n
  · simp only [indicator_of_mem hx, sub_self, norm_zero, add_zero, le_refl]
  · simp only [indicator_of_notMem hx]
    exact le_add_of_nonneg_left (norm_nonneg _)

#print axioms weighted_transposedGreen_joint_truncation

end HarmonicBalls
