import HarmonicBalls.Proofs.Potential.GeneralDomainFiniteSourceCorrection
import HarmonicBalls.Proofs.Potential.LogPotentialExceptionalSet
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Whole-plane source truncation for observation measures

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- The whole-plane kernel is product-integrable on bounded observer sets. -/
theorem wholePlane_observation_kernel_integrable_product {K V : Set ℂ} {μ ν : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β)) (hK : IsCompact K) (hν : ν Kᶜ = 0)
    (hV : Bornology.IsBounded V) :
    Integrable (fun p : ℂ × ℂ => greenFunction univ p.1 p.2)
      (ν.prod (μ.restrict V)) := by
  obtain ⟨r, hr⟩ := (hK.isBounded.union hV).subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : K ∪ V ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  have hνR : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν] with y hy
    exact ball_subset_closedBall (hsub (Or.inl (by simpa using hy)))
  obtain ⟨r₀, β, hr₀, hβ, hg⟩ := hup R hR
  have hp := log_integrable_product_of_upper (ν := ν) hR hr₀ hβ hg
    (measure_ball_lt_top (μ := μ)).ne
  rw [Measure.restrict_eq_self_of_ae_mem hνR] at hp
  have hp' := hp.mono_measure (Measure.prod_mono le_rfl
    (Measure.restrict_mono (show V ⊆ ball (0 : ℂ) R from fun x hx => hsub (Or.inr hx)) le_rfl))
  have hp'' := hp'.const_mul (-(2 * Real.pi)⁻¹)
  convert hp'' using 1
  funext p
  simp only [greenFunction_univ_eq_newtonKernel, newtonKernel]

/-- On a bounded observer set, the full and truncated source kernels are
integrable at almost every observer, and their potentials are integrable. -/
theorem wholePlane_observation_source_integrability {K V : Set ℂ} {μ ν : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (hK : IsCompact K) (hν : ν Kᶜ = 0) (hV : Bornology.IsBounded V)
    (E : ℕ → Set ℂ) :
    (∀ᵐ x ∂(μ.restrict V), Integrable (fun y => greenFunction univ y x) ν ∧
      ∀ n, Integrable (fun y => greenFunction univ y x) (ν.restrict (E n))) ∧
    Integrable (greenPotential univ ν) (μ.restrict V) ∧
    ∀ n, Integrable (greenPotential univ (ν.restrict (E n))) (μ.restrict V) := by
  have hp := wholePlane_observation_kernel_integrable_product hup hK hν hV
  have heq (ρ : Measure ℂ) (x : ℂ) : greenPotential univ ρ x =
      ∫ y, greenFunction univ y x ∂ρ := by
    simp only [greenPotential, greenFunction_univ_eq_newtonKernel, newtonKernel_comm]
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hp.prod_left_ae] with x hx
    exact ⟨hx, fun n => hx.mono_measure Measure.restrict_le_self⟩
  · rw [show greenPotential univ ν = _ from funext (heq ν)]
    exact hp.integral_prod_right
  · intro n
    rw [show greenPotential univ (ν.restrict (E n)) = _ from funext (heq _)]
    exact (hp.mono_measure (Measure.prod_mono (Measure.restrict_le_self) le_rfl)).integral_prod_right

/-- Truncation on a bounded observer set converges almost everywhere and in L1. -/
theorem wholePlane_observation_source_truncation_on {K V : Set ℂ} {μ ν : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β)) (hK : IsCompact K) (hν : ν Kᶜ = 0)
    (hV : Bornology.IsBounded V) (E : ℕ → Set ℂ)
    (hE : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hcover : ∀ᵐ y ∂ν, y ∈ ⋃ n, E n) :
    (∀ᵐ x ∂(μ.restrict V),
      Tendsto (fun n => greenPotential univ (ν.restrict (E n)) x) atTop
        (𝓝 (greenPotential univ ν x))) ∧
    Tendsto (fun n => ∫ x in V, ‖greenPotential univ (ν.restrict (E n)) x -
      greenPotential univ ν x‖ ∂μ) atTop (𝓝 0) := by
  have hp := wholePlane_observation_kernel_integrable_product hup hK hν hV
  have hf := hp.integral_prod_right
  have hnorm := hp.norm.integral_prod_right
  have hi (n : ℕ) : Integrable (fun x => ∫ y in E n, greenFunction univ y x ∂ν)
      (μ.restrict V) := by
    exact (hp.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)).integral_prod_right
  have hpoint : ∀ᵐ x ∂(μ.restrict V),
      Tendsto (fun n => ∫ y in E n, greenFunction univ y x ∂ν) atTop
        (𝓝 (∫ y, greenFunction univ y x ∂ν)) := by
    filter_upwards [hp.prod_left_ae] with x hx
    have hc : ∀ᵐ y ∂ν, ∃ N, ∀ n ≥ N, y ∈ E n := by
      filter_upwards [hcover] with y hy
      obtain ⟨N, hN⟩ := mem_iUnion.mp hy
      exact ⟨N, fun n hn => hmono hn hN⟩
    have hd := tendsto_integral_of_dominated_convergence
      (μ := ν) (F := fun n => (E n).indicator (fun y => greenFunction univ y x))
      (f := fun y => greenFunction univ y x) (fun y => ‖greenFunction univ y x‖)
      (fun n => hx.aestronglyMeasurable.indicator (hE n)) hx.norm
      (fun n => Filter.Eventually.of_forall fun y => by
        by_cases hy : y ∈ E n <;> simp [hy])
      (hc.mono fun y hy => by
        obtain ⟨N, hN⟩ := hy
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_ge_atTop N] with n hn
        simp [hN n hn])
    simpa only [integral_indicator (hE _)] using hd
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := μ.restrict V) (fun x => 2 * ∫ y, ‖greenFunction univ y x‖ ∂ν)
    (fun n => ((hi n).sub hf).norm.aestronglyMeasurable) (hnorm.const_mul 2)
    (fun n => by
      filter_upwards [hp.prod_left_ae] with x hx
      have ha := norm_integral_le_integral_norm (μ := ν.restrict (E n)) (fun y => greenFunction univ y x)
      have hb := norm_integral_le_integral_norm (μ := ν) (fun y => greenFunction univ y x)
      have hc : (∫ y in E n, ‖greenFunction univ y x‖ ∂ν) ≤
          ∫ y, ‖greenFunction univ y x‖ ∂ν :=
        integral_mono_measure Measure.restrict_le_self
          (Filter.Eventually.of_forall fun y => norm_nonneg _) hx.norm
      change ‖‖(∫ y in E n, greenFunction univ y x ∂ν) -
        (∫ y, greenFunction univ y x ∂ν)‖‖ ≤ _
      rw [norm_norm]
      calc
        ‖(∫ y in E n, greenFunction univ y x ∂ν) -
          (∫ y, greenFunction univ y x ∂ν)‖ ≤
            ‖∫ y in E n, greenFunction univ y x ∂ν‖ +
              ‖∫ y, greenFunction univ y x ∂ν‖ := norm_sub_le _ _
        _ ≤ 2 * ∫ y, ‖greenFunction univ y x‖ ∂ν := by linarith)
    (hpoint.mono fun x hx => by simpa using (hx.sub tendsto_const_nhds).norm)
  have heq (μ : Measure ℂ) (x : ℂ) : greenPotential univ μ x =
      ∫ y, greenFunction univ y x ∂μ := by
    simp only [greenPotential, greenFunction_univ_eq_newtonKernel, newtonKernel_comm]
  constructor
  · filter_upwards [hpoint] with x hx
    simpa only [heq] using hx
  · simpa [heq] using hlim

/-- Source truncations converge at observation-almost every point of the plane. -/
theorem wholePlane_observation_source_truncation_ae {K : Set ℂ} {μ ν : Measure ℂ}
    [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β)) (hK : IsCompact K) (hν : ν Kᶜ = 0)
    (E : ℕ → Set ℂ) (hE : ∀ n, MeasurableSet (E n))
    (hmono : Monotone E) (hcover : ∀ᵐ y ∂ν, y ∈ ⋃ n, E n) :
    ∀ᵐ x ∂μ, Tendsto (fun n => greenPotential univ (ν.restrict (E n)) x)
      atTop (𝓝 (greenPotential univ ν x)) := by
  have h := (ae_restrict_iUnion_iff (μ := μ)
    (fun n : ℕ => ball (0 : ℂ) n) _).2 (fun n =>
      (wholePlane_observation_source_truncation_on hup hK hν isBounded_ball E hE hmono hcover).1)
  simpa only [Metric.iUnion_ball_nat, Measure.restrict_univ] using h

#print axioms wholePlane_observation_kernel_integrable_product
#print axioms wholePlane_observation_source_integrability
#print axioms wholePlane_observation_source_truncation_on
#print axioms wholePlane_observation_source_truncation_ae

end HarmonicBalls
