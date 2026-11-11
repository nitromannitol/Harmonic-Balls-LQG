import HarmonicBalls.Proofs.Potential.GeneralDomainFiniteSourceCorrection
import HarmonicBalls.Proofs.Potential.LogPotentialExceptionalSet
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Whole-plane source truncation

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- The whole-plane kernel is product-integrable on bounded observer sets. -/
theorem wholePlane_kernel_integrable_product {K V : Set ℂ} {ν : Measure ℂ}
    [IsFiniteMeasure ν] (hK : IsCompact K) (hν : ν Kᶜ = 0)
    (hV : Bornology.IsBounded V) :
    Integrable (fun p : ℂ × ℂ => greenFunction univ p.1 p.2)
      (ν.prod (volume.restrict V)) := by
  obtain ⟨r, hr⟩ := (hK.isBounded.union hV).subset_ball (0 : ℂ)
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsub : K ∪ V ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
  have hνR : ∀ᵐ y ∂ν, y ∈ closedBall (0 : ℂ) R := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hν] with y hy
    exact ball_subset_closedBall (hsub (Or.inl (by simpa using hy)))
  obtain ⟨_, _, r₀, hr₀, hg⟩ := volumeGrowth_volume R
  have hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      volume (ball z r) ≤ ENNReal.ofReal (r ^ (1 : ℝ)) := by
    intro r hr hrr z hz
    exact (hg r hr hrr z hz).2
  have hp := log_integrable_product_of_upper (ν := ν) hR hr₀
    (by norm_num : (0 : ℝ) < 1) hup (measure_ball_lt_top (μ := volume)).ne
  rw [Measure.restrict_eq_self_of_ae_mem hνR] at hp
  have hp' := hp.mono_measure (Measure.prod_mono le_rfl
    (Measure.restrict_mono (show V ⊆ ball (0 : ℂ) R from fun x hx => hsub (Or.inr hx)) le_rfl))
  have hp'' := hp'.const_mul (-(2 * Real.pi)⁻¹)
  convert hp'' using 1
  funext p
  simp only [greenFunction_univ_eq_newtonKernel, newtonKernel]

/-- Truncation on a bounded observer set converges almost everywhere and in L1. -/
theorem wholePlane_source_truncation_on {K V : Set ℂ} {ν : Measure ℂ}
    [IsFiniteMeasure ν] (hK : IsCompact K) (hν : ν Kᶜ = 0)
    (hV : Bornology.IsBounded V) (E : ℕ → Set ℂ)
    (hE : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hcover : ∀ᵐ y ∂ν, y ∈ ⋃ n, E n) :
    (∀ᵐ x ∂(volume.restrict V),
      Tendsto (fun n => greenPotential univ (ν.restrict (E n)) x) atTop
        (𝓝 (greenPotential univ ν x))) ∧
    Tendsto (fun n => ∫ x in V, ‖greenPotential univ (ν.restrict (E n)) x -
      greenPotential univ ν x‖) atTop (𝓝 0) := by
  have hp := wholePlane_kernel_integrable_product hK hν hV
  have hf := hp.integral_prod_right
  have hnorm := hp.norm.integral_prod_right
  have hi (n : ℕ) : Integrable (fun x => ∫ y in E n, greenFunction univ y x ∂ν)
      (volume.restrict V) := by
    exact (hp.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)).integral_prod_right
  have hpoint : ∀ᵐ x ∂(volume.restrict V),
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
    (μ := volume.restrict V) (fun x => 2 * ∫ y, ‖greenFunction univ y x‖ ∂ν)
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

/-- Source truncations converge at volume-almost every point of the plane. -/
theorem wholePlane_source_truncation_ae {K : Set ℂ} {ν : Measure ℂ}
    [IsFiniteMeasure ν] (hK : IsCompact K) (hν : ν Kᶜ = 0)
    (E : ℕ → Set ℂ) (hE : ∀ n, MeasurableSet (E n))
    (hmono : Monotone E) (hcover : ∀ᵐ y ∂ν, y ∈ ⋃ n, E n) :
    ∀ᵐ x ∂volume, Tendsto (fun n => greenPotential univ (ν.restrict (E n)) x)
      atTop (𝓝 (greenPotential univ ν x)) := by
  have h := (ae_restrict_iUnion_iff (μ := volume)
    (fun n : ℕ => ball (0 : ℂ) n) _).2 (fun n =>
      (wholePlane_source_truncation_on hK hν isBounded_ball E hE hmono hcover).1)
  simpa only [Metric.iUnion_ball_nat, Measure.restrict_univ] using h


end HarmonicBalls
