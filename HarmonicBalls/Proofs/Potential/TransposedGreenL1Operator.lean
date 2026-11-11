import HarmonicBalls.Proofs.Potential.IntegrableDensityTransposedLaplacian

/-! # Transposed Green operator on L¹

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/
namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped Topology

/-- A common row-mass constant controls the L¹ norm of each weighted potential. -/
theorem integrable_density_transposedGreen_bound {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], (∀ᵐ y ∂ν, y ∈ V) →
      ∀ (f : ℂ → ℝ), Measurable f → Integrable f ν →
      IntegrableOn (fun x => ∫ y, f y * greenFunction V y x ∂ν) V ∧
      (∫ x in V, ‖∫ y, f y * greenFunction V y x ∂ν‖) ≤
        C * ∫ y, |f y| ∂ν := by
  obtain ⟨C, hC, hmass⟩ := transposedGreen_mass_bound hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν f hf hfi0
  have hVb : Bornology.IsBounded V := isBounded_ball.subset hsub
  have hp := integrable_density_transposedGreen_product hV hVb hν hf hfi0
  have ha := integrable_density_transposedGreen_product hV hVb hν hf.norm hfi0.norm
  have hfi : Integrable (fun y => |f y|) ν := by simpa only [Real.norm_eq_abs] using hfi0.norm
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


/-- The Green potential defines a bounded linear operator on every L¹ source class. -/
theorem existsUnique_transposedGreen_L1_operator {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], (∀ᵐ y ∂ν, y ∈ V) →
      ∃! T : Lp ℝ 1 ν →L[ℝ] Lp ℝ 1 (volume.restrict V),
        (∀ f, T f =ᵐ[volume.restrict V]
          fun x => ∫ y, f y * greenFunction V y x ∂ν) ∧
        (∀ (f : Lp ℝ 1 ν) (g : ℂ → ℝ), f =ᵐ[ν] g → T f =ᵐ[volume.restrict V]
          fun x => ∫ y, g y * greenFunction V y x ∂ν) ∧ ‖T‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := integrable_density_transposedGreen_bound hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν
  let P : Lp ℝ 1 ν → ℂ → ℝ := fun f x => ∫ y, f y * greenFunction V y x ∂ν
  have hi (f : Lp ℝ 1 ν) : Integrable (P f) (volume.restrict V) :=
    (hbound hV hsub ν hν f (L1.measurable_coeFn f) (L1.integrable_coeFn f)).1
  have hp (f : Lp ℝ 1 ν) : Integrable (fun p : ℂ × ℂ => f p.1 * greenFunction V p.1 p.2)
      (ν.prod (volume.restrict V)) :=
    integrable_density_transposedGreen_product hV (isBounded_ball.subset hsub) hν
      (L1.measurable_coeFn f) (L1.integrable_coeFn f)
  let F : Lp ℝ 1 ν → Lp ℝ 1 (volume.restrict V) := fun f => (hi f).toL1 (P f)
  have hF (f : Lp ℝ 1 ν) : F f =ᵐ[volume.restrict V] P f := (hi f).coeFn_toL1
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
  let L : Lp ℝ 1 ν →ₗ[ℝ] Lp ℝ 1 (volume.restrict V) :=
    { toFun := F
      map_add' := hadd
      map_smul' := hsmul }
  have hn (f : Lp ℝ 1 ν) : ‖L f‖ ≤ C * ‖f‖ := by
    rw [L1.norm_eq_integral_norm, L1.norm_eq_integral_norm]
    have heq : (∫ x, ‖L f x‖ ∂(volume.restrict V)) =
        ∫ x, ‖P f x‖ ∂(volume.restrict V) := by
      apply integral_congr_ae
      filter_upwards [hF f] with x hx
      rw [show L f x = F f x from rfl, hx]
    rw [heq]
    simpa only [Real.norm_eq_abs] using
      (hbound hV hsub ν hν f (L1.measurable_coeFn f) (L1.integrable_coeFn f)).2
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
