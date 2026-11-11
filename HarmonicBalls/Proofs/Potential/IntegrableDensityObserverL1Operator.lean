import HarmonicBalls.Proofs.Potential.IntegrableDensityObserverBound

/-! # Green operator on L¹ for observers with local upper growth

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Topology

/-- The Green potential defines a bounded linear operator on every L¹ source class. -/
theorem existsUnique_integrable_density_observer_L1_operator
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], (∀ᵐ y ∂ν, y ∈ V) →
      ∃! T : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 (μ.restrict V),
        (∀ f, T f =ᵐ[μ.restrict V]
          fun x => ∫ y, f y * greenFunction V y x ∂ν) ∧
        (∀ (f : Lp ℝ 1 ν) (g : ℂ → ℝ), f =ᵐ[ν] g → T f =ᵐ[μ.restrict V]
          fun x => ∫ y, g y * greenFunction V y x ∂ν) ∧ ‖T‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := integrable_density_observer_bound hup hR
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


end HarmonicBalls
