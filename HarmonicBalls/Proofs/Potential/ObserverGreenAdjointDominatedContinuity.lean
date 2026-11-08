import HarmonicBalls.Proofs.Potential.ObserverGreenLInfinityAdjoint
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Dominated continuity of the observer Green adjoint

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

/-- Bounded observer densities converging almost everywhere yield almost everywhere
convergence of their Green adjoints, and convergence under every integrable source test. -/
theorem observer_green_adjoint_dominated_continuity
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) {V : Set ℂ} (hV : IsOpen V)
    (hsub : V ⊆ ball 0 R) (hν : ∀ᵐ y ∂ν, y ∈ V)
    (S : Lp ℝ ∞ (μ.restrict V) →L[ℝ] Lp ℝ ∞ ν)
    (hS : ∀ g, S g =ᵐ[ν] fun y => ∫ x in V, greenFunction V y x * g x ∂μ)
    (gs : ℕ → Lp ℝ ∞ (μ.restrict V)) (g : Lp ℝ ∞ (μ.restrict V))
    (M : ℝ) (hM : ∀ n, ‖gs n‖ ≤ M)
    (hconv : ∀ᵐ x ∂μ.restrict V, Tendsto (fun n => gs n x) atTop (𝓝 (g x))) :
    (∀ᵐ y ∂ν, Tendsto (fun n => S (gs n) y) atTop (𝓝 (S g y))) ∧
    ∀ f : Lp ℝ 1 ν, Tendsto (fun n => ∫ y, f y * (S (gs n) y - S g y) ∂ν)
      atTop (𝓝 0) := by
  have hM0 : 0 ≤ M := (norm_nonneg (gs 0)).trans (hM 0)
  obtain ⟨C, hC, hrow⟩ := green_row_bound_of_local_upper_growth hup hR
  obtain ⟨D, hD, hbounded⟩ := bounded_observer_green_row hup hR
  have hgs (n : ℕ) : ∀ᵐ x ∂μ.restrict V, ‖gs n x‖ ≤ M := by
    filter_upwards [show ∀ᵐ x ∂μ.restrict V, ‖gs n x‖ ≤ ‖gs n‖ from by
      simpa only [lpNorm, Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp (gs n))] with x hx
    exact hx.trans (hM n)
  have hpoint : ∀ y ∈ V, Tendsto
      (fun n => ∫ x in V, greenFunction V y x * gs n x ∂μ) atTop
      (𝓝 (∫ x in V, greenFunction V y x * g x ∂μ)) := by
    intro y hy
    apply tendsto_integral_of_dominated_convergence
      (fun x => M * greenFunction V y x)
    · intro n
      exact (((measurable_greenFunction_uncurry hV).comp
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable (gs n)))
    · exact ((hrow hV hsub y hy).1).const_mul M
    · intro n
      filter_upwards [hgs n] with x hx
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg
        (greenFunction_nonneg (isBounded_ball.subset hsub) y x)]
      nlinarith [greenFunction_nonneg (isBounded_ball.subset hsub) y x]
    · filter_upwards [hconv] with x hx
      exact tendsto_const_nhds.mul hx
  have hpointS : ∀ᵐ y ∂ν, Tendsto (fun n => S (gs n) y) atTop (𝓝 (S g y)) := by
    filter_upwards [hν, hS g, ae_all_iff.mpr (fun n => hS (gs n))] with y hy hg hgn
    simpa only [hg, hgn] using hpoint y hy
  refine ⟨hpointS, ?_⟩
  intro f
  have hbound (n : ℕ) : ∀ᵐ y ∂ν, ‖S (gs n) y‖ ≤ D * M := by
    filter_upwards [hν, hS (gs n)] with y hy heq
    rw [heq]
    exact ((hbounded hV hsub (gs n) y hy).2).trans (mul_le_mul_of_nonneg_left (hM n) hD)
  have hpair : Tendsto (fun n => ∫ y, f y * S (gs n) y ∂ν) atTop
      (𝓝 (∫ y, f y * S g y ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun y => (D * M) * ‖f y‖)
    · intro n
      exact (Lp.aestronglyMeasurable f).mul (Lp.aestronglyMeasurable (S (gs n)))
    · exact (L1.integrable_coeFn f).norm.const_mul _
    · intro n
      filter_upwards [hbound n] with y hy
      rw [norm_mul]
      nlinarith [norm_nonneg (f y)]
    · filter_upwards [hpointS] with y hy
      exact tendsto_const_nhds.mul hy
  have hint (k : Lp ℝ ∞ ν) : Integrable (fun y => f y * k y) ν := by
    apply (L1.integrable_coeFn f).mul_bdd (Lp.aestronglyMeasurable k)
    simpa only [lpNorm, Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp k)
  have heq (n : ℕ) : (∫ y, f y * (S (gs n) y - S g y) ∂ν) =
      (∫ y, f y * S (gs n) y ∂ν) - ∫ y, f y * S g y ∂ν := by
    simp only [mul_sub, integral_sub (hint _) (hint _)]
  simp_rw [heq]
  simpa only [sub_self] using hpair.sub (tendsto_const_nhds (x := ∫ y, f y * S g y ∂ν))

/-- The same convergence holds for arbitrary almost-everywhere representatives and
for the mixed Green integrals in either order. -/
theorem observer_green_adjoint_representative_dominated_continuity
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) {V : Set ℂ} (hV : IsOpen V)
    (hsub : V ⊆ ball 0 R) (hν : ∀ᵐ y ∂ν, y ∈ V)
    (T : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 (μ.restrict V))
    (hT : ∀ f, T f =ᵐ[μ.restrict V] fun x => ∫ y, f y * greenFunction V y x ∂ν)
    (S : Lp ℝ ∞ (μ.restrict V) →L[ℝ] Lp ℝ ∞ ν)
    (hS : ∀ g, S g =ᵐ[ν] fun y => ∫ x in V, greenFunction V y x * g x ∂μ)
    (gs : ℕ → Lp ℝ ∞ (μ.restrict V)) (g : Lp ℝ ∞ (μ.restrict V))
    (gs' : ℕ → ℂ → ℝ) (g' : ℂ → ℝ)
    (hreps : ∀ n, gs n =ᵐ[μ.restrict V] gs' n) (hrep : g =ᵐ[μ.restrict V] g')
    (M : ℝ) (hM : ∀ n, ‖gs n‖ ≤ M)
    (hconv : ∀ᵐ x ∂μ.restrict V, Tendsto (fun n => gs' n x) atTop (𝓝 (g' x)))
    (f : Lp ℝ 1 ν) (f' : ℂ → ℝ) (hf : f =ᵐ[ν] f') :
    (∀ᵐ y ∂ν, Tendsto (fun n => ∫ x in V, greenFunction V y x * gs' n x ∂μ)
      atTop (𝓝 (∫ x in V, greenFunction V y x * g' x ∂μ))) ∧
    Tendsto (fun n => ∫ y, f' y * ((∫ x in V, greenFunction V y x * gs' n x ∂μ) -
      (∫ x in V, greenFunction V y x * g' x ∂μ)) ∂ν) atTop (𝓝 0) ∧
    Tendsto (fun n => ∫ x in V, (∫ y, f' y * greenFunction V y x ∂ν) *
      (gs' n x - g' x) ∂μ) atTop (𝓝 0) := by
  have hc : ∀ᵐ x ∂μ.restrict V, Tendsto (fun n => gs n x) atTop (𝓝 (g x)) := by
    filter_upwards [hconv, hrep, ae_all_iff.mpr hreps] with x hx hg hgs
    simpa only [hg, hgs] using hx
  obtain ⟨hp, ht⟩ := observer_green_adjoint_dominated_continuity hup hR hV hsub hν S hS gs g M hM hc
  have hsrep (k : Lp ℝ ∞ (μ.restrict V)) (k' : ℂ → ℝ)
      (hk : k =ᵐ[μ.restrict V] k') :
      S k =ᵐ[ν] fun y => ∫ x in V, greenFunction V y x * k' x ∂μ := by
    filter_upwards [hS k] with y hy
    rw [hy]
    apply integral_congr_ae
    filter_upwards [hk] with x hx
    rw [hx]
  have hs := hsrep g g' hrep
  have hss n := hsrep (gs n) (gs' n) (hreps n)
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hp, hs, ae_all_iff.mpr hss] with y hy hg hgs
    simpa only [hg, hgs] using hy
  · have heq (n : ℕ) :
        (∫ y, f' y * ((∫ x in V, greenFunction V y x * gs' n x ∂μ) -
          (∫ x in V, greenFunction V y x * g' x ∂μ)) ∂ν) =
        ∫ y, f y * (S (gs n) y - S g y) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hf, hs, hss n] with y hfy hgy hny
      rw [← hfy, ← hgy, ← hny]
    simp_rw [heq]
    exact ht f
  · have hint (k : Lp ℝ ∞ (μ.restrict V)) :
        Integrable (fun x => T f x * k x) (μ.restrict V) := by
      apply (L1.integrable_coeFn (T f)).mul_bdd (Lp.aestronglyMeasurable k)
      simpa only [lpNorm, Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp k)
    have htf : T f =ᵐ[μ.restrict V] fun x => ∫ y, f' y * greenFunction V y x ∂ν := by
      filter_upwards [hT f] with x hx
      rw [hx]
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      rw [hy]
    have heq (n : ℕ) :
        (∫ x in V, (∫ y, f' y * greenFunction V y x ∂ν) * (gs' n x - g' x) ∂μ) =
        ∫ y, f y * (S (gs n) y - S g y) ∂ν := by
      calc
        _ = ∫ x in V, T f x * (gs n x - g x) ∂μ := by
          apply integral_congr_ae
          filter_upwards [htf, hreps n, hrep] with x hx hn hg
          rw [← hx, ← hn, ← hg]
        _ = (∫ x in V, T f x * gs n x ∂μ) - ∫ x in V, T f x * g x ∂μ := by
          simp only [mul_sub, integral_sub (hint _) (hint _)]
        _ = (∫ y, f y * S (gs n) y ∂ν) - ∫ y, f y * S g y ∂ν := by
          rw [observer_green_Linfinity_duality hup hV (isBounded_ball.subset hsub) hν T hT S hS f (gs n),
            observer_green_Linfinity_duality hup hV (isBounded_ball.subset hsub) hν T hT S hS f g]
        _ = ∫ y, f y * (S (gs n) y - S g y) ∂ν := by
          have hi (k : Lp ℝ ∞ ν) : Integrable (fun y => f y * k y) ν := by
            apply (L1.integrable_coeFn f).mul_bdd (Lp.aestronglyMeasurable k)
            simpa only [lpNorm, Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp k)
          simp only [mul_sub, integral_sub (hi _) (hi _)]
    simp_rw [heq]
    exact ht f

#print axioms observer_green_adjoint_representative_dominated_continuity
#print axioms observer_green_adjoint_dominated_continuity
end HarmonicBalls
