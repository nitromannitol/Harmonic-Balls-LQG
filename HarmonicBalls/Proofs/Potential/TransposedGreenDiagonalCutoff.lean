import HarmonicBalls.Proofs.Potential.FiniteSourceObservationIntegrability
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Diagonal cutoffs of transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

/-- Distance cutoffs preserve mixed integrability and converge at almost every
observer and in observer L¹. The Green kernel is in source-observer order. -/
theorem transposedGreen_diagonal_cutoff
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    (∀ n, Measurable (fun p : ℂ × ℂ =>
      if δ n < dist p.1 p.2 then greenFunction V p.1 p.2 else 0)) ∧
    (∀ n, Integrable (fun p : ℂ × ℂ =>
      if δ n < dist p.1 p.2 then greenFunction V p.1 p.2 else 0)
      (ν.prod (μ.restrict V))) ∧
    (∀ᵐ x ∂μ.restrict V, Integrable (fun y => greenFunction V y x) ν ∧
      (∀ n, Integrable (fun y => if δ n < dist y x then greenFunction V y x else 0) ν) ∧
      Tendsto (fun n => ∫ y, if δ n < dist y x then greenFunction V y x else 0 ∂ν)
        atTop (𝓝 (∫ y, greenFunction V y x ∂ν))) ∧
    Tendsto (fun n => ∫ x in V, ‖(∫ y, if δ n < dist y x then
      greenFunction V y x else 0 ∂ν) - (∫ y, greenFunction V y x ∂ν)‖ ∂μ)
      atTop (𝓝 0) := by
  let A (n : ℕ) : Set (ℂ × ℂ) := {p | δ n < dist p.1 p.2}
  let G : ℂ × ℂ → ℝ := fun p => greenFunction V p.1 p.2
  have hA (n : ℕ) : MeasurableSet (A n) := measurableSet_lt measurable_const measurable_dist
  have hmeas (n : ℕ) : Measurable ((A n).indicator G) :=
    (measurable_greenFunction_uncurry hV).indicator (hA n)
  have hp : Integrable G (ν.prod (μ.restrict V)) :=
    generalDomain_green_integrable_product_of_local_upper_growth hup hV hVb hν
  have hi (n : ℕ) : Integrable ((A n).indicator G) (ν.prod (μ.restrict V)) :=
    hp.indicator (hA n)
  have hkernel (y x : ℂ) : Tendsto (fun n => (A n).indicator G (y, x)) atTop
      (𝓝 (greenFunction V y x)) := by
    by_cases hyx : y = x
    · subst y
      simp [A, G, Set.indicator_apply, greenFunction_self]
    · apply tendsto_const_nhds.congr'
      filter_upwards [hδ.eventually (eventually_lt_nhds (dist_pos.mpr hyx))] with n hn
      simp [A, G, hn]
  have hpoint : ∀ᵐ x ∂μ.restrict V, Integrable (fun y => greenFunction V y x) ν ∧
      (∀ n, Integrable (fun y => (A n).indicator G (y, x)) ν) ∧
      Tendsto (fun n => ∫ y, (A n).indicator G (y, x) ∂ν) atTop
        (𝓝 (∫ y, greenFunction V y x ∂ν)) := by
    filter_upwards [hp.prod_left_ae, ae_all_iff.mpr (fun n => (hi n).prod_left_ae)] with x hx hix
    refine ⟨hx, hix, ?_⟩
    apply tendsto_integral_of_dominated_convergence (fun y => ‖greenFunction V y x‖)
      (fun n => (hix n).aestronglyMeasurable) hx.norm
    · intro n
      filter_upwards [] with y
      by_cases h : δ n < dist y x <;> simp [A, G, h]
    · exact Eventually.of_forall (fun y => hkernel y x)
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := μ.restrict V) (fun x => 2 * ∫ y, ‖greenFunction V y x‖ ∂ν)
    (fun n => (((hi n).integral_prod_right).sub hp.integral_prod_right).norm.aestronglyMeasurable)
    (hp.norm.integral_prod_right.const_mul 2)
    (fun n => by
      filter_upwards [hp.prod_left_ae, (hi n).prod_left_ae] with x hx hix
      have hb : (∫ y, ‖(A n).indicator G (y, x)‖ ∂ν) ≤
          ∫ y, ‖greenFunction V y x‖ ∂ν := by
        apply integral_mono_ae hix.norm hx.norm
        filter_upwards [] with y
        by_cases h : δ n < dist y x <;> simp [A, G, h]
      change ‖‖(∫ y, (A n).indicator G (y, x) ∂ν) -
        (∫ y, greenFunction V y x ∂ν)‖‖ ≤ _
      rw [norm_norm]
      have ha := norm_integral_le_integral_norm (μ := ν) (fun y => (A n).indicator G (y, x))
      have hc := norm_integral_le_integral_norm (μ := ν) (fun y => greenFunction V y x)
      have hd := norm_sub_le (∫ y, (A n).indicator G (y, x) ∂ν)
        (∫ y, greenFunction V y x ∂ν)
      linarith)
    (hpoint.mono fun x hx => by simpa using (hx.2.2.sub tendsto_const_nhds).norm)
  have heq (n : ℕ) : (A n).indicator G = (fun p =>
      if δ n < dist p.1 p.2 then greenFunction V p.1 p.2 else 0) := by
    funext p
    simp [A, G, Set.indicator_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rw [← heq n]
    exact hmeas n
  · intro n
    rw [← heq n]
    exact hi n
  · filter_upwards [hpoint] with x hx
    simpa [A, G, Set.indicator_apply] using hx
  · simpa [A, G, Set.indicator_apply] using hlim

#print axioms transposedGreen_diagonal_cutoff

end HarmonicBalls
