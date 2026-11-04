import HarmonicBalls.Proofs.Sec5.CircleAverageMeasurability
import HarmonicBalls.Proofs.Sec5.GaussianProcessLaw

/-! # Measurable reconstruction of LQG approximations -/

namespace HarmonicBalls

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

/-- A continuous circle-average profile determines its LQG approximation by a
measurable map on the space of all profiles with the evaluation σ-algebra. -/
theorem exists_measurable_lqgApprox_decoder (γ r : ℝ) :
    ∃ F : (ℂ → ℝ) → Measure ℂ, Measurable F ∧
      ∀ u : ℂ → ℝ, Continuous u → F u = lqgApprox γ (fun _ => u) r := by
  classical
  let A : ℕ → SimpleFunc ℂ ℂ := (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).approx
  have hA : ∀ z : ℂ, Tendsto (fun n => A n z) atTop (𝓝 z) :=
    (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).tendsto_approx
  have hm : ∀ n, Measurable (fun p : (ℂ → ℝ) × ℂ => p.1 (A n p.2)) := by
    intro n
    have h : Measurable (fun p : (ℂ → ℝ) × (A n).range => p.1 p.2) :=
      measurable_from_prod_countable_left fun z => measurable_pi_apply z.1
    have hAmeas : Measurable (fun p : (ℂ → ℝ) × ℂ =>
        (⟨A n p.2, SimpleFunc.mem_range_self _ _⟩ : (A n).range)) :=
      Measurable.subtype_mk ((A n).measurable.comp measurable_snd)
    have heval := h.comp (measurable_fst.prodMk hAmeas)
    exact heval
  let D : (ℂ → ℝ) → ℂ → ℝ≥0∞ := fun u z =>
    Filter.liminf (fun n => ENNReal.ofReal (r ^ (γ ^ 2 / 2) * Real.exp (γ * u (A n z)))) atTop
  have hD : Measurable (Function.uncurry D) := by
    apply Measurable.liminf
    intro n
    exact (measurable_const.mul ((measurable_const.mul (hm n)).exp)).ennreal_ofReal
  refine ⟨fun u => volume.withDensity (D u), measurable_withDensity hD, ?_⟩
  intro u hu
  simp only [lqgApprox]
  congr 1
  funext z
  apply Filter.Tendsto.liminf_eq
  exact (ENNReal.continuous_ofReal.tendsto _).comp
    ((tendsto_const_nhds.mul (Real.continuous_exp.tendsto _ |>.comp
      (tendsto_const_nhds.mul ((hu.tendsto z).comp (hA z))))))

/-- The singular-field circle-average profile is almost surely continuous
at every fixed positive radius. -/
theorem IsWholePlaneGFF.ae_continuous_fieldCircleAverage
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ ω ∂P, Continuous (fun z => fieldCircleAverage α₀ (hcirc ω) r z) := by
  filter_upwards [h.ae_continuousOn_circle] with ω hω
  have hc : Continuous (fun z : ℂ => hcirc ω r z) :=
    hω.comp_continuous (continuous_const.prodMk continuous_id) (fun z => ⟨hr, Set.mem_univ z⟩)
  simp_rw [fieldCircleAverage_eq _ _ hr]
  exact hc.sub (continuous_const.mul ((continuous_const.max continuous_norm).log
    fun z => (lt_max_of_lt_left hr).ne'))

/-- For every positive regularization radius, the LQG approximations of the
original and normalized rescaled fields have the same law. -/
theorem IsWholePlaneGFF.identDistrib_normalizedScale_lqgApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (γ α₀ : ℝ)
    {k r : ℝ} (hk : 0 < k) (hr : 0 < r) :
    IdentDistrib
      (fun ω => lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) r)
      (fun ω => lqgApprox γ (fieldCircleAverage α₀
        (fun s z => hcirc ω (k * s) (k • z) - hcirc ω k 0)) r) P P := by
  obtain ⟨F, hF, hF_eq⟩ := exists_measurable_lqgApprox_decoder γ r
  let v : ({r : ℝ // 0 < r} × ℂ → ℝ) → ℂ → ℝ := fun f z => f (⟨r, hr⟩, z)
  have hv : Measurable v := Measurable.of_eval fun z =>
    measurable_pi_apply ((⟨r, hr⟩ : {r : ℝ // 0 < r}), z)
  have hd := ((h.identDistrib_normalizedScale_fieldCircleProcess hAff α₀ hk).comp hv).comp hF
  have hscaled := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hc₁ := h.ae_continuous_fieldCircleAverage α₀ hr
  have hc₂ := hscaled.ae_continuous_fieldCircleAverage α₀ hr
  have heq₁ : (F ∘ v ∘ fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
      fieldCircleAverage α₀ (hcirc ω) p.1 p.2) =ᵐ[P]
      (fun ω => lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) r) := by
    filter_upwards [hc₁] with ω hω
    exact hF_eq _ hω
  have heq₂ : (F ∘ v ∘ fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
      fieldCircleAverage α₀ (fun s z => hcirc ω (k * s) (k • z) - hcirc ω k 0) p.1 p.2) =ᵐ[P]
      (fun ω => lqgApprox γ (fieldCircleAverage α₀
        (fun s z => hcirc ω (k * s) (k • z) - hcirc ω k 0)) r) := by
    filter_upwards [hc₂] with ω hω
    apply hF_eq
    simpa only [Function.comp_def, v, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, add_zero,
      Complex.real_smul] using hω
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq₁).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq₂)

/-- The entire sequence of dyadic LQG approximations has the same law after
normalized rescaling. -/
theorem IsWholePlaneGFF.identDistrib_normalizedScale_lqgApproxSequence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc) (γ α₀ : ℝ)
    {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n))
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀
        (fun s z => hcirc ω (k * s) (k • z) - hcirc ω k 0)) (dyadicScale n)) P P := by
  classical
  choose F hF hFeq using fun n : ℕ => exists_measurable_lqgApprox_decoder γ (dyadicScale n)
  let v : ({r : ℝ // 0 < r} × ℂ → ℝ) → ℕ → Measure ℂ :=
    fun f n => F n (fun z => f (⟨dyadicScale n, dyadicScale_pos n⟩, z))
  have hv : Measurable v := by
    apply Measurable.of_eval
    intro n
    apply (hF n).comp
    apply Measurable.of_eval
    intro z
    exact measurable_pi_apply ((⟨dyadicScale n, dyadicScale_pos n⟩ : {r : ℝ // 0 < r}), z)
  have hd := (h.identDistrib_normalizedScale_fieldCircleProcess hAff α₀ hk).comp hv
  have hscaled := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hc₁ := ae_all_iff.2 fun n => h.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  have hc₂ := ae_all_iff.2 fun n => hscaled.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  have heq₁ : (v ∘ fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
      fieldCircleAverage α₀ (hcirc ω) p.1 p.2) =ᵐ[P]
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n)) := by
    filter_upwards [hc₁] with ω hω
    funext n
    exact hFeq n _ (hω n)
  have heq₂ : (v ∘ fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) =>
      fieldCircleAverage α₀ (fun s z => hcirc ω (k * s) (k • z) - hcirc ω k 0) p.1 p.2) =ᵐ[P]
      (fun ω n => lqgApprox γ (fieldCircleAverage α₀
        (fun s z => hcirc ω (k * s) (k • z) - hcirc ω k 0)) (dyadicScale n)) := by
    filter_upwards [hc₂] with ω hω
    funext n
    apply hFeq
    simpa only [Function.comp_def, v, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk,
      add_zero, Complex.real_smul] using hω n
  exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq₁).symm.trans hd).trans
    (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq₂)

end HarmonicBalls
