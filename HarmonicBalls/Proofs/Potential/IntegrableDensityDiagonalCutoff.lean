import HarmonicBalls.Proofs.Potential.IntegrableDensityTransposedLaplacian
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Diagonal cutoffs for integrable-density Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Topology

/-- Distance cutoffs converge in product L¹ and at almost every observer, and
also converge in observer L¹. The kernel is in source-observer order. -/
theorem integrable_density_diagonal_cutoff
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) (hfi : Integrable f ν)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (volume.restrict V)) ∧
    (∀ n, Integrable (fun p : ℂ × ℂ =>
      if ε n ≤ dist p.1 p.2 then f p.1 * greenFunction V p.1 p.2 else 0)
      (ν.prod (volume.restrict V))) ∧
    Integrable (fun x => ∫ y, f y * greenFunction V y x ∂ν) (volume.restrict V) ∧
    (∀ n, Integrable (fun x => ∫ y, if ε n ≤ dist y x then
      f y * greenFunction V y x else 0 ∂ν) (volume.restrict V)) ∧
    Tendsto (fun n => ∫ p, ‖(if ε n ≤ dist p.1 p.2 then
      f p.1 * greenFunction V p.1 p.2 else 0) -
      f p.1 * greenFunction V p.1 p.2‖ ∂(ν.prod (volume.restrict V))) atTop (𝓝 0) ∧
    (∀ᵐ x ∂volume.restrict V,
      Integrable (fun y => f y * greenFunction V y x) ν ∧
      (∀ n, Integrable (fun y => if ε n ≤ dist y x then
        f y * greenFunction V y x else 0) ν) ∧
      Tendsto (fun n => ∫ y, if ε n ≤ dist y x then
        f y * greenFunction V y x else 0 ∂ν) atTop
        (𝓝 (∫ y, f y * greenFunction V y x ∂ν))) ∧
    Tendsto (fun n => ∫ x in V, ‖(∫ y, if ε n ≤ dist y x then
      f y * greenFunction V y x else 0 ∂ν) -
      (∫ y, f y * greenFunction V y x ∂ν)‖) atTop (𝓝 0) := by
  let A (n : ℕ) : Set (ℂ × ℂ) := {p | ε n ≤ dist p.1 p.2}
  let G : ℂ × ℂ → ℝ := fun p => f p.1 * greenFunction V p.1 p.2
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_le measurable_const measurable_dist
  have hp : Integrable G (ν.prod (volume.restrict V)) :=
    integrable_density_transposedGreen_product hV hVb hν hf hfi
  have hi (n : ℕ) : Integrable ((A n).indicator G) (ν.prod (volume.restrict V)) :=
    hp.indicator (hA n)
  have hkernel (y x : ℂ) : Tendsto (fun n => (A n).indicator G (y, x)) atTop
      (𝓝 (G (y, x))) := by
    by_cases hyx : y = x
    · subst y
      simp [A, G, Set.indicator_apply, greenFunction_self]
    · apply tendsto_const_nhds.congr'
      filter_upwards [hε.eventually (eventually_lt_nhds (dist_pos.mpr hyx))] with n hn
      simp [A, G, le_of_lt hn]
  have hpoint : ∀ᵐ x ∂volume.restrict V, Integrable (fun y => G (y, x)) ν ∧
      (∀ n, Integrable (fun y => (A n).indicator G (y, x)) ν) ∧
      Tendsto (fun n => ∫ y, (A n).indicator G (y, x) ∂ν) atTop
        (𝓝 (∫ y, G (y, x) ∂ν)) := by
    filter_upwards [hp.prod_left_ae, ae_all_iff.mpr (fun n => (hi n).prod_left_ae)] with x hx hix
    refine ⟨hx, hix, ?_⟩
    apply tendsto_integral_of_dominated_convergence (fun y => ‖G (y, x)‖)
      (fun n => (hix n).aestronglyMeasurable) hx.norm
    · intro n
      filter_upwards with y
      by_cases h : ε n ≤ dist y x <;> simp [A, h]
    · exact Eventually.of_forall (fun y => hkernel y x)
  have hprod := tendsto_integral_of_dominated_convergence
    (μ := ν.prod (volume.restrict V)) (fun p => ‖G p‖)
    (fun n => ((hi n).sub hp).norm.aestronglyMeasurable) hp.norm
    (fun n => by
      filter_upwards with p
      by_cases h : ε n ≤ dist p.1 p.2 <;> simp [A, h])
    (Eventually.of_forall fun p => by
      simpa using ((hkernel p.1 p.2).sub tendsto_const_nhds).norm)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict V) (fun x => 2 * ∫ y, ‖G (y, x)‖ ∂ν)
    (fun n => (((hi n).integral_prod_right).sub hp.integral_prod_right).norm.aestronglyMeasurable)
    (hp.norm.integral_prod_right.const_mul 2)
    (fun n => by
      filter_upwards [hp.prod_left_ae, (hi n).prod_left_ae] with x hx hix
      have hb : (∫ y, ‖(A n).indicator G (y, x)‖ ∂ν) ≤ ∫ y, ‖G (y, x)‖ ∂ν := by
        apply integral_mono_ae hix.norm hx.norm
        filter_upwards with y
        by_cases h : ε n ≤ dist y x <;> simp [A, h]
      change ‖‖(∫ y, (A n).indicator G (y, x) ∂ν) - (∫ y, G (y, x) ∂ν)‖‖ ≤ _
      rw [norm_norm]
      have ha := norm_integral_le_integral_norm (μ := ν) (fun y => (A n).indicator G (y, x))
      have hc := norm_integral_le_integral_norm (μ := ν) (fun y => G (y, x))
      have hd := norm_sub_le (∫ y, (A n).indicator G (y, x) ∂ν) (∫ y, G (y, x) ∂ν)
      linarith)
    (hpoint.mono fun x hx => by simpa using (hx.2.2.sub tendsto_const_nhds).norm)
  have heq (n : ℕ) : (A n).indicator G = (fun p =>
      if ε n ≤ dist p.1 p.2 then f p.1 * greenFunction V p.1 p.2 else 0) := by
    funext p
    simp [A, G, Set.indicator_apply]
  refine ⟨hp, ?_, hp.integral_prod_right, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [← heq n]
    exact hi n
  · intro n
    simpa [A, G, Set.indicator_apply] using (hi n).integral_prod_right
  · simpa [A, G, Set.indicator_apply] using hprod
  · filter_upwards [hpoint] with x hx
    simpa [A, G, Set.indicator_apply] using hx
  · simpa [A, G, Set.indicator_apply] using hlim

end HarmonicBalls
