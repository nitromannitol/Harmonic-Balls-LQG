import HarmonicBalls.Proofs.Potential.TransposedGreenMassBound

/-!
# Weighted transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- A bounded source weight preserves mixed integrability of the Green kernel. -/
theorem weighted_transposedGreen_integrable_product {V : Set ℂ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    {ν : Measure ℂ} [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    {f : ℂ → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, ‖f y‖ ≤ B) :
    Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (volume.restrict V)) := by
  exact (generalDomain_green_integrable_product_volume hV hVb hν).bdd_mul
    (hf.comp measurable_fst).aestronglyMeasurable (Eventually.of_forall fun p => hB p.1)

/-- A common row-mass constant controls the L¹ norm of each weighted potential. -/
theorem weighted_transposedGreen_bound {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], (∀ᵐ y ∂ν, y ∈ V) →
      ∀ (f : ℂ → ℝ), Measurable f → (∃ B, ∀ y, ‖f y‖ ≤ B) →
      IntegrableOn (fun x => ∫ y, f y * greenFunction V y x ∂ν) V ∧
      (∫ x in V, ‖∫ y, f y * greenFunction V y x ∂ν‖) ≤
        C * ∫ y, |f y| ∂ν := by
  obtain ⟨C, hC, hmass⟩ := transposedGreen_mass_bound hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν f hf ⟨B, hB⟩
  have hVb : Bornology.IsBounded V := isBounded_ball.subset hsub
  have hp := weighted_transposedGreen_integrable_product hV hVb hν hf hB
  have ha := weighted_transposedGreen_integrable_product hV hVb hν hf.norm (fun y => by simpa using hB y)
  have hfi : Integrable (fun y => |f y|) ν := by
    apply (integrable_const B).mono' hf.norm.aestronglyMeasurable
    exact Eventually.of_forall fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (f y))] using hB y
  let μ := ν.withDensity (fun y => ENNReal.ofReal |f y|)
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity_ofReal hfi.2
  have hμ : ∀ᵐ y ∂μ, y ∈ V :=
    (withDensity_absolutelyContinuous ν _).ae_le hν
  have hm := hmass hV hsub μ hμ
  have hmass_eq : (μ Set.univ).toReal = ∫ y, |f y| ∂ν := by
    dsimp [μ]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfi (Eventually.of_forall fun y => abs_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun y => abs_nonneg _)]
  have heq (x : ℂ) : (∫ y, greenFunction V y x ∂μ) =
      ∫ y, ‖f y‖ * greenFunction V y x ∂ν := by
    dsimp [μ]
    rw [integral_withDensity_eq_integral_toReal_smul (hf.abs.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) ]
    simp [ENNReal.toReal_ofReal, abs_nonneg, smul_eq_mul]
  refine ⟨hp.integral_prod_right, ?_⟩
  calc
    (∫ x in V, ‖∫ y, f y * greenFunction V y x ∂ν‖) ≤
        ∫ x in V, ∫ y, ‖f y‖ * greenFunction V y x ∂ν := by
      apply integral_mono_ae hp.integral_prod_right.norm ha.integral_prod_right
      filter_upwards with x
      calc
        ‖∫ y, f y * greenFunction V y x ∂ν‖ ≤ ∫ y, ‖f y * greenFunction V y x‖ ∂ν := norm_integral_le_integral_norm _
        _ = ∫ y, ‖f y‖ * greenFunction V y x ∂ν := by
          apply integral_congr_ae
          filter_upwards with y
          simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg hVb y x)]
    _ = ∫ x in V, ∫ y, greenFunction V y x ∂μ := by simp only [heq]
    _ ≤ C * ∫ y, |f y| ∂ν := by simpa only [hmass_eq] using hm.2.2.2.2

/-- L¹ convergence of bounded source densities implies L¹ convergence of the
corresponding transposed Green potentials. -/
theorem tendsto_weighted_transposedGreen_of_L1 {R : ℝ} (hR : 0 < R)
    {V : Set ℂ} (hV : IsOpen V) (hsub : V ⊆ ball 0 R)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hν : ∀ᵐ y ∂ν, y ∈ V)
    (f : ℕ → ℂ → ℝ) (g : ℂ → ℝ)
    (hf : ∀ n, Measurable (f n)) (hg : Measurable g)
    (hfb : ∀ n, ∃ B, ∀ y, ‖f n y‖ ≤ B) (hgb : ∃ B, ∀ y, ‖g y‖ ≤ B)
    (hlim : Tendsto (fun n => ∫ y, |f n y - g y| ∂ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in V, ‖(∫ y, f n y * greenFunction V y x ∂ν) -
      (∫ y, g y * greenFunction V y x ∂ν)‖) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := weighted_transposedGreen_bound hR
  have hlim' : Tendsto (fun n => C * ∫ y, |f n y - g y| ∂ν) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hlim
  apply squeeze_zero (fun n => integral_nonneg fun x => norm_nonneg _) _ hlim'
  intro n
  obtain ⟨B, hB⟩ := hfb n
  obtain ⟨D, hD⟩ := hgb
  have hd : ∃ K, ∀ y, ‖f n y - g y‖ ≤ K := by
    refine ⟨B + D, fun y => ?_⟩
    exact (norm_sub_le _ _).trans (add_le_add (hB y) (hD y))
  have hb := (hbound hV hsub ν hν (fun y => f n y - g y) ((hf n).sub hg) hd).2
  have hVb : Bornology.IsBounded V := isBounded_ball.subset hsub
  have hp := weighted_transposedGreen_integrable_product hV hVb hν (hf n) hB
  have hq := weighted_transposedGreen_integrable_product hV hVb hν hg hD
  have heq : (∫ x in V, ‖(∫ y, f n y * greenFunction V y x ∂ν) -
      (∫ y, g y * greenFunction V y x ∂ν)‖) =
      ∫ x in V, ‖∫ y, (f n y - g y) * greenFunction V y x ∂ν‖ := by
    apply integral_congr_ae
    filter_upwards [hp.prod_left_ae, hq.prod_left_ae] with x hx hy
    congr 1
    rw [← integral_sub hx hy]
    congr 1
    funext y
    ring
  rw [heq]
  exact hb


end HarmonicBalls
