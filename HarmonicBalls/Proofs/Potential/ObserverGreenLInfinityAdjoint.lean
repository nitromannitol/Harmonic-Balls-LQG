import HarmonicBalls.Proofs.Potential.IntegrableDensityObserverL1Operator
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! # Green operator on bounded observer densities

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

/-- A bounded observer density is integrable against each Green row, with a
uniform bound on its integral. -/
theorem bounded_observer_green_row
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (g : Lp ℝ ∞ (μ.restrict V)) y, y ∈ V →
      Integrable (fun x => greenFunction V y x * g x) (μ.restrict V) ∧
      ‖∫ x in V, greenFunction V y x * g x ∂μ‖ ≤ C * ‖g‖ := by
  obtain ⟨C, hC, hrow⟩ := green_row_bound_of_local_upper_growth hup hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub g y hy
  have hVb := isBounded_ball.subset hsub
  have hg : ∀ᵐ x ∂μ.restrict V, ‖g x‖ ≤ ‖g‖ := by
    simpa only [lpNorm, Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp g)
  have hi := (hrow hV hsub y hy).1
  have hm : AEStronglyMeasurable (fun x => greenFunction V y x * g x) (μ.restrict V) :=
    (((measurable_greenFunction_uncurry hV).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable g))
  have hh : ∀ᵐ x ∂μ.restrict V,
      ‖greenFunction V y x * g x‖ ≤ ‖g‖ * greenFunction V y x := by
    filter_upwards [hg] with x hx
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (greenFunction_nonneg hVb y x)]
    nlinarith [greenFunction_nonneg hVb y x]
  have hip : Integrable (fun x => greenFunction V y x * g x) (μ.restrict V) :=
    (hi.const_mul ‖g‖).mono' hm hh
  refine ⟨hip, ?_⟩
  calc
    ‖∫ x in V, greenFunction V y x * g x ∂μ‖ ≤
        ∫ x in V, ‖greenFunction V y x * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in V, ‖g‖ * greenFunction V y x ∂μ :=
      integral_mono_ae hip.norm (hi.const_mul ‖g‖) hh
    _ = ‖g‖ * (∫ x in V, greenFunction V y x ∂μ) := integral_const_mul _ _
    _ ≤ C * ‖g‖ := by nlinarith [(hrow hV hsub y hy).2, norm_nonneg g]

/-- The Green rows define a bounded operator on bounded observer densities. -/
theorem existsUnique_observer_green_Linfinity_operator
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], (∀ᵐ y ∂ν, y ∈ V) →
      ∃! S : Lp ℝ ∞ (μ.restrict V) →L[ℝ] Lp ℝ ∞ ν,
        (∀ g, S g =ᵐ[ν] fun y => ∫ x in V, greenFunction V y x * g x ∂μ) ∧
        (∀ (g : Lp ℝ ∞ (μ.restrict V)) (g' : ℂ → ℝ), g =ᵐ[μ.restrict V] g' →
          S g =ᵐ[ν] fun y => ∫ x in V, greenFunction V y x * g' x ∂μ) ∧ ‖S‖ ≤ C := by
  obtain ⟨C, hC, hrow⟩ := bounded_observer_green_row hup hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν
  let P : Lp ℝ ∞ (μ.restrict V) → ℂ → ℝ :=
    fun g y => ∫ x in V, greenFunction V y x * g x ∂μ
  have hm (g : Lp ℝ ∞ (μ.restrict V)) : AEStronglyMeasurable (P g) ν := by
    exact (((measurable_greenFunction_uncurry hV).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable g).comp_snd).integral_prod_right')
  have hb (g : Lp ℝ ∞ (μ.restrict V)) : ∀ᵐ y ∂ν, ‖P g y‖ ≤ C * ‖g‖ := by
    filter_upwards [hν] with y hy
    exact (hrow hV hsub g y hy).2
  have hp (g : Lp ℝ ∞ (μ.restrict V)) : MemLp (P g) ∞ ν :=
    memLp_top_of_bound (hm g) (C * ‖g‖) (hb g)
  let F : Lp ℝ ∞ (μ.restrict V) → Lp ℝ ∞ ν := fun g => (hp g).toLp (P g)
  have hF (g : Lp ℝ ∞ (μ.restrict V)) : F g =ᵐ[ν] P g := (hp g).coeFn_toLp
  have hadd (g k : Lp ℝ ∞ (μ.restrict V)) : F (g + k) = F g + F k := by
    apply Lp.ext
    filter_upwards [hν, hF (g + k), hF g, hF k, Lp.coeFn_add (F g) (F k)]
      with y hy hgk hg hk hs
    rw [hgk, hs, Pi.add_apply, hg, hk]
    change (∫ x in V, greenFunction V y x * (g + k) x ∂μ) = _
    rw [← integral_add (hrow hV hsub g y hy).1 (hrow hV hsub k y hy).1]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add g k] with x hx
    rw [hx, Pi.add_apply, mul_add]
  have hsmul (c : ℝ) (g : Lp ℝ ∞ (μ.restrict V)) : F (c • g) = c • F g := by
    apply Lp.ext
    filter_upwards [hF (c • g), hF g, Lp.coeFn_smul c (F g)] with y hcg hg hs
    rw [hcg, hs, Pi.smul_apply, hg]
    change (∫ x in V, greenFunction V y x * (c • g) x ∂μ) = c * (∫ x in V, greenFunction V y x * g x ∂μ)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c g] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  let L : Lp ℝ ∞ (μ.restrict V) →ₗ[ℝ] Lp ℝ ∞ ν :=
    { toFun := F, map_add' := hadd, map_smul' := hsmul }
  have hn (g : Lp ℝ ∞ (μ.restrict V)) : ‖L g‖ ≤ C * ‖g‖ := by
    have h := Lp.norm_le_of_ae_bound (mul_nonneg hC (norm_nonneg g))
      (show ∀ᵐ y ∂ν, ‖L g y‖ ≤ C * ‖g‖ from by
        filter_upwards [hF g, hb g] with y heq hy
        change ‖F g y‖ ≤ _
        rw [heq]
        exact hy)
    simpa only [ENNReal.toReal_top, inv_zero, NNReal.rpow_zero, NNReal.coe_one, Real.rpow_zero, one_mul] using h
  let S := L.mkContinuous C hn
  refine ⟨S, ⟨hF, ?_, LinearMap.mkContinuous_norm_le L hC hn⟩, ?_⟩
  · intro g g' hgg'
    filter_upwards [hF g] with y hy
    change F g y = _
    rw [hy]
    apply integral_congr_ae
    filter_upwards [hgg'] with x hx
    rw [hx]
  intro S hS
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.ext
  exact (hS.1 g).trans (hF g).symm

/-- The Green row operator is adjoint to the source-to-observer operator. -/
theorem observer_green_Linfinity_duality
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [IsFiniteMeasure ν]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {V : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hν : ∀ᵐ y ∂ν, y ∈ V)
    (T : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 (μ.restrict V))
    (hT : ∀ f, T f =ᵐ[μ.restrict V] fun x => ∫ y, f y * greenFunction V y x ∂ν)
    (S : Lp ℝ ∞ (μ.restrict V) →L[ℝ] Lp ℝ ∞ ν)
    (hS : ∀ g, S g =ᵐ[ν] fun y => ∫ x in V, greenFunction V y x * g x ∂μ)
    (f : Lp ℝ 1 ν) (g : Lp ℝ ∞ (μ.restrict V)) :
    (∫ x in V, T f x * g x ∂μ) = ∫ y, f y * S g y ∂ν := by
  have hp := integrable_density_green_product_of_local_upper_growth hup hV hVb hν
    (L1.measurable_coeFn f) (L1.integrable_coeFn f)
  have hg : ∀ᵐ x ∂μ.restrict V, ‖g x‖ ≤ ‖g‖ := by
    simpa only [lpNorm, Lp.norm_def] using ae_le_lpNorm_exponent_top (Lp.memLp g)
  have hgp : ∀ᵐ p ∂ν.prod (μ.restrict V), ‖g p.2‖ ≤ ‖g‖ :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := μ.restrict V)).ae hg
  have hmix : Integrable (fun p : ℂ × ℂ => (f p.1 * greenFunction V p.1 p.2) * g p.2)
      (ν.prod (μ.restrict V)) := hp.mul_bdd (Lp.aestronglyMeasurable g).comp_snd hgp
  calc
    (∫ x in V, T f x * g x ∂μ) =
        ∫ x in V, (∫ y, f y * greenFunction V y x ∂ν) * g x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hT f] with x hx
      rw [hx]
    _ = ∫ x in V, ∫ y, (f y * greenFunction V y x) * g x ∂ν ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_mul_const]
    _ = ∫ y, ∫ x in V, (f y * greenFunction V y x) * g x ∂μ ∂ν :=
      (integral_integral_swap hmix).symm
    _ = ∫ y, f y * (∫ x in V, greenFunction V y x * g x ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    _ = ∫ y, f y * S g y ∂ν := by
      apply integral_congr_ae
      filter_upwards [hS g] with y hy
      rw [hy]

end HarmonicBalls
