import HarmonicBalls.Proofs.Potential.SigmaFiniteSourceObserverDensity
import HarmonicBalls.Proofs.Potential.ObserverGreenLInfinityAdjoint

/-! # Green operators for sigma-finite sources

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Topology ENNReal

/-- The Green potential defines a bounded linear operator on every L¹ source class. -/
theorem existsUnique_sigmaFinite_integrable_density_observer_L1_operator
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [SigmaFinite ν], (∀ᵐ y ∂ν, y ∈ V) →
      ∃! T : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 (μ.restrict V),
        (∀ f, T f =ᵐ[μ.restrict V]
          fun x => ∫ y, f y * greenFunction V y x ∂ν) ∧
        (∀ (f : Lp ℝ 1 ν) (g : ℂ → ℝ), f =ᵐ[ν] g → T f =ᵐ[μ.restrict V]
          fun x => ∫ y, g y * greenFunction V y x ∂ν) ∧ ‖T‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := sigmaFinite_integrable_density_observer_bound hup hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν
  let P : Lp ℝ 1 ν → ℂ → ℝ := fun f x => ∫ y, f y * greenFunction V y x ∂ν
  have hi (f : Lp ℝ 1 ν) : Integrable (P f) (μ.restrict V) :=
    (hbound hV hsub hν (L1.measurable_coeFn f) (L1.integrable_coeFn f)).2.2.1
  have hp (f : Lp ℝ 1 ν) : Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (μ.restrict V)) :=
    (hbound hV hsub hν (L1.measurable_coeFn f) (L1.integrable_coeFn f)).1
  let F : Lp ℝ 1 ν → Lp ℝ 1 (μ.restrict V) := fun f => (hi f).toL1 (P f)
  have hF (f : Lp ℝ 1 ν) : F f =ᵐ[μ.restrict V] P f := (hi f).coeFn_toL1
  have hadd (f g : Lp ℝ 1 ν) : F (f + g) = F f + F g := by
    apply Lp.ext
    filter_upwards [hF (f + g), hF f, hF g, Lp.coeFn_add (F f) (F g),
      (hp f).prod_left_ae, (hp g).prod_left_ae] with x hfg hf hg hs hfi hgi
    rw [hfg, hs, Pi.add_apply, hf, hg]
    change (∫ y, (f + g) y * greenFunction V y x ∂ν) = _
    rw [← integral_add hfi hgi]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_add f g] with y hy
    rw [hy, Pi.add_apply, add_mul]
  have hsmul (c : ℝ) (f : Lp ℝ 1 ν) : F (c • f) = c • F f := by
    apply Lp.ext
    filter_upwards [hF (c • f), hF f, Lp.coeFn_smul c (F f)] with x hcf hf hs
    rw [hcf, hs, Pi.smul_apply, hf]
    change (∫ y, (c • f) y * greenFunction V y x ∂ν) = c * (∫ y, f y * greenFunction V y x ∂ν)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_smul c f] with y hy
    rw [hy]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  let L : Lp ℝ 1 ν →ₗ[ℝ] Lp ℝ 1 (μ.restrict V) :=
    { toFun := F
      map_add' := hadd
      map_smul' := hsmul }
  have hn (f : Lp ℝ 1 ν) : ‖L f‖ ≤ C * ‖f‖ := by
    rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
    have heq : (∫ x, ‖L f x‖ ∂(μ.restrict V)) =
        ∫ x, ‖P f x‖ ∂(μ.restrict V) := by
      apply integral_congr_ae
      filter_upwards [hF f] with x hx
      rw [show L f x = F f x from rfl, hx]
    rw [heq]
    simpa only [Real.norm_eq_abs] using
      (hbound hV hsub hν (L1.measurable_coeFn f) (L1.integrable_coeFn f)).2.2.2
  let T := L.mkContinuous C hn
  refine ⟨T, ⟨hF, ?_, LinearMap.mkContinuous_norm_le L hC hn⟩, ?_⟩
  · intro f g hfg
    filter_upwards [hF f] with x hx
    change F f x = _
    rw [hx]
    apply integral_congr_ae
    filter_upwards [hfg] with y hy
    rw [hy]
  intro S hS
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (hS.1 f).trans (hF f).symm

/-- The Green rows define a bounded operator on bounded observer densities. -/
theorem existsUnique_sigmaFinite_observer_green_Linfinity_operator
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [SigmaFinite ν], (∀ᵐ y ∂ν, y ∈ V) →
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
    have hb' : ∀ᵐ y ∂ν, ‖L g y‖ ≤ C * ‖g‖ := by
      filter_upwards [hF g, hb g] with y heq hy
      change ‖F g y‖ ≤ _
      rw [heq]
      exact hy
    rw [Lp.norm_def, eLpNorm_exponent_top (Lp.aestronglyMeasurable (L g))]
    exact (ENNReal.toReal_le_toReal (by simpa only [eLpNorm_exponent_top (Lp.aestronglyMeasurable (L g))] using Lp.eLpNorm_ne_top (L g)) ENNReal.ofReal_ne_top).2
      (eLpNormEssSup_le_of_ae_bound hb') |>.trans_eq
        (ENNReal.toReal_ofReal (mul_nonneg hC (norm_nonneg g)))
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
theorem sigmaFinite_observer_green_Linfinity_duality
    {μ ν : Measure ℂ} [IsLocallyFiniteMeasure μ] [SigmaFinite ν]
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
  have hp := sigmaFinite_integrable_density_green_product_of_local_upper_growth hup hV hVb hν
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

#print axioms existsUnique_sigmaFinite_integrable_density_observer_L1_operator
#print axioms existsUnique_sigmaFinite_observer_green_Linfinity_operator
#print axioms sigmaFinite_observer_green_Linfinity_duality

end HarmonicBalls
