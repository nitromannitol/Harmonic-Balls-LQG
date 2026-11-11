import HarmonicBalls.Proofs.Sec6.PotentialRatioLaw

/-! # Laws of affine images of whole-plane LQG measures

The LQG measure is a measurable limit of the circle-average approximations;
therefore the law of the whole-plane GFF determines its measure law.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Two whole-plane GFFs on the same space have identically distributed
sequences of LQG approximations. -/
theorem identDistrib_lqgApproxSequence_of_gff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P hC' hcirc') (γ : ℝ) :
    IdentDistrib
      (fun ω n => lqgApprox γ (fieldCircleAverage 0 (hcirc ω)) (dyadicScale n))
      (fun ω n => lqgApprox γ (fieldCircleAverage 0 (hcirc' ω)) (dyadicScale n)) P P := by
  classical
  let v : {r : ℝ // 0 < r} × ℂ → GFFObservable.Admissible :=
    fun p => ⟨.circle p.1 p.2, p.1.2⟩
  have hv : Measurable (fun f : GFFObservable.Admissible → ℝ => fun p => f (v p)) :=
    Measurable.of_eval fun p => measurable_pi_apply (v p)
  have hd := (h.identDistrib_observables h').comp hv
  choose F hF hFeq using fun n : ℕ => exists_measurable_lqgApprox_decoder γ (dyadicScale n)
  let D : ({r : ℝ // 0 < r} × ℂ → ℝ) → ℕ → Measure ℂ :=
    fun f n => F n (fun z => f (⟨dyadicScale n, dyadicScale_pos n⟩, z))
  have hD : Measurable D := by
    apply Measurable.of_eval
    intro n
    apply (hF n).comp
    apply Measurable.of_eval
    intro z
    exact measurable_pi_apply ((⟨dyadicScale n, dyadicScale_pos n⟩ : {r : ℝ // 0 < r}), z)
  have hdist := hd.comp hD
  have hc := ae_all_iff.2 fun n => h.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n)
  have hc' := ae_all_iff.2 fun n => h'.ae_continuous_fieldCircleAverage 0 (dyadicScale_pos n)
  have heq : (D ∘ (fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) => hcirc ω p.1 p.2)) =ᵐ[P]
      (fun ω n => lqgApprox γ (fieldCircleAverage 0 (hcirc ω)) (dyadicScale n)) := by
    filter_upwards [hc] with ω hω
    funext n
    simpa only [Function.comp_def, D, v, GFFObservable.eval, fieldCircleAverage_zero, lqgApprox] using hFeq n _ (hω n)
  have heq' : (D ∘ (fun (ω : Ω) (p : {r : ℝ // 0 < r} × ℂ) => hcirc' ω p.1 p.2)) =ᵐ[P]
      (fun ω n => lqgApprox γ (fieldCircleAverage 0 (hcirc' ω)) (dyadicScale n)) := by
    filter_upwards [hc'] with ω hω
    funext n
    simpa only [Function.comp_def, D, v, GFFObservable.eval, fieldCircleAverage_zero, lqgApprox] using hFeq n _ (hω n)
  exact ((IdentDistrib.of_ae_eq hdist.aemeasurable_fst heq).symm.trans hdist).trans
    (IdentDistrib.of_ae_eq hdist.aemeasurable_snd heq')

/-- Compactly supported continuous test integrals have the same joint law
for LQG measures of two whole-plane GFFs. -/
theorem identDistrib_lqg_testIntegrals_of_gff
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω} {γ : ℝ}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    {μ ν : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) (hν : IsLQGMeasureOfField P γ 0 hcirc' ν)
    {f : ι → ℂ → ℝ} (hf : ∀ i, Continuous (f i)) (hfc : ∀ i, HasCompactSupport (f i)) :
    IdentDistrib (fun ω i => ∫ z, f i z ∂(μ ω)) (fun ω i => ∫ z, f i z ∂(ν ω)) P P := by
  let _ := h.isGaussianProcess.isProbabilityMeasure
  let K : Kernel (Measure ℂ) ℂ := ⟨id, measurable_id⟩
  have hint : Measurable (fun (m : Measure ℂ) i => ∫ z, f i z ∂m) := by
    apply Measurable.of_eval
    intro i
    exact ((hf i).stronglyMeasurable.integral_kernel (κ := K)).measurable
  let X : ℕ → Ω → ι → ℝ := fun n ω i =>
    ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage 0 (hcirc ω)) (dyadicScale n))
  let Y : ℕ → Ω → ι → ℝ := fun n ω i =>
    ∫ z, f i z ∂(lqgApprox γ (fieldCircleAverage 0 (hcirc' ω)) (dyadicScale n))
  let U : Ω → ι → ℝ := fun ω i => ∫ z, f i z ∂(μ ω)
  let V : Ω → ι → ℝ := fun ω i => ∫ z, f i z ∂(ν ω)
  have hd (n : ℕ) : IdentDistrib (X n) (Y n) P P := by
    simpa only [Function.comp_def, X, Y] using
      ((identDistrib_lqgApproxSequence_of_gff h h' γ).comp (measurable_pi_apply n)).comp hint
  have hx : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (U ω)) := by
    filter_upwards [hμ] with ω hω
    apply tendsto_pi_nhds.mpr
    intro i
    exact hω.tendsto_integral (f i) (hf i) (hfc i)
  have hy : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (V ω)) := by
    filter_upwards [hν] with ω hω
    apply tendsto_pi_nhds.mpr
    intro i
    exact hω.tendsto_integral (f i) (hf i) (hfc i)
  have hu : AEMeasurable U P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hd n).aemeasurable_fst) hx
  have hv : AEMeasurable V P :=
    aemeasurable_of_tendsto_metrizable_ae atTop (fun n => (hd n).aemeasurable_snd) hy
  have hxu := tendstoInDistribution_of_ae_tendsto (fun n => (hd n).aemeasurable_fst) hu hx
  have hyv := tendstoInDistribution_of_ae_tendsto (fun n => (hd n).aemeasurable_snd) hv hy
  have hxv : TendstoInDistribution X atTop V (fun _ => P) P := by
    refine ⟨fun n => (hd n).aemeasurable_fst, hv, ?_⟩
    convert! hyv.tendsto using 1
    congr 1
    funext n
    apply Subtype.ext
    exact (hd n).map_eq
  exact ⟨hu, hv, tendstoInDistribution_unique X hxu hxv⟩

/-- Whole-plane GFFs determine the law of their LQG measures. -/
theorem identDistrib_lqgMeasure_of_gff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    {μ ν : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (h' : IsWholePlaneGFF P hC' hcirc')
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) (hν : IsLQGMeasureOfField P γ 0 hcirc' ν) :
    IdentDistrib μ ν P P := by
  classical
  let _ := h.isGaussianProcess.isProbabilityMeasure
  apply identDistrib_of_open_masses (h.aemeasurable_lqgMeasure hμ) (h'.aemeasurable_lqgMeasure hν)
  · filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  · filter_upwards [hν] with ω hω
    exact hω.isLocallyFiniteMeasure
  · intro ι _ U hU
    choose f hf hfc hmass using fun i => exists_open_mass_test_functions (hU i)
    let F : (ι × ℕ → ℝ) → ι → ℝ≥0∞ := fun x i => ⨆ n, ENNReal.ofReal (x (i, n))
    have hF : Measurable F := by
      apply Measurable.of_eval
      intro i
      exact Measurable.iSup fun n => (measurable_pi_apply (i, n)).ennreal_ofReal
    have hd := (identDistrib_lqg_testIntegrals_of_gff h h' hμ hν
      (f := fun p : ι × ℕ => f p.1 p.2) (fun p => hf p.1 p.2)
      (fun p => hfc p.1 p.2)).comp hF
    have heq₁ : (F ∘ fun ω p => ∫ z, f p.1 p.2 z ∂(μ ω)) =ᵐ[P]
        (fun ω i => μ ω (U i)) := by
      filter_upwards [hμ] with ω hω
      funext i
      exact (hmass i (μ ω) hω.isLocallyFiniteMeasure).symm
    have heq₂ : (F ∘ fun ω p => ∫ z, f p.1 p.2 z ∂(ν ω)) =ᵐ[P]
        (fun ω i => ν ω (U i)) := by
      filter_upwards [hν] with ω hω
      funext i
      exact (hmass i (ν ω) hω.isLocallyFiniteMeasure).symm
    exact ((IdentDistrib.of_ae_eq hd.aemeasurable_fst heq₁).symm.trans hd).trans
      (IdentDistrib.of_ae_eq hd.aemeasurable_snd heq₂)

/-- The normalized affine pullback of a whole-plane LQG measure has the same
law as the original measure. The affine GFF and LQG coordinate-change inputs
are assumptions. -/
theorem identDistrib_affineMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IdentDistrib μ (affineMeasure γ hcirc μ a b) P P := by
  have hs : IsWholePlaneGFF P (affinePairing hC hcirc a b) (affineCircle hcirc a b) :=
    hAff h a ha b
  exact identDistrib_lqgMeasure_of_gff h hs hμ
    (isLQGMeasureOfField_affine hCC h hγ hγ2 hμ ha b)

universe u

/-- On a fixed smooth domain, pulling back the whole-plane LQG measure by any
complex affine map preserves the law of the Green-potential extrema ratio. -/
theorem identDistrib_lqg_greenPotentialExtremaRatio_affine
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) {O K : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hK : K ⊆ closure O) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio O K (μ ω))
      (fun ω => greenPotentialExtremaRatio O K ((μ ω).map (fun z => (z - b) / a))) P P := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  have hs : IsWholePlaneGFF P (affinePairing hC hcirc a b) (affineCircle hcirc a b) :=
    hAff h a ha b
  have hsμ := isLQGMeasureOfField_affine hCC h hγ hγ2 hμ ha b
  have hd := identDistrib_greenPotentialExtremaRatio
    (identDistrib_affineMeasure h hμ hAff hCC hγ hγ2 ha b) hopen hO.1
    (ae_continuous_lqg_greenPotential_extrema hholder hγ hγ2 hQ h hμ hO hK)
    (ae_continuous_lqg_greenPotential_extrema hholder hγ hγ2 hQ hs hsμ hO hK)
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [affineMeasure, greenPotentialExtremaRatio]
  apply greenPotential_extrema_ratio_smul_measure
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  · exact ENNReal.ofReal_ne_top

/-- A pointwise Green-function similarity transfers potentials by the
corresponding measurable pullback of the measure. -/
theorem greenPotential_of_greenFunction_pullback
    {O O' : Set ℂ} (hO : IsOpen O) (μ : Measure ℂ) (f g : ℂ → ℂ)
    (hg : Measurable g)
    (hgreen : ∀ x y, greenFunction O' (f x) y = greenFunction O x (g y)) (x : ℂ) :
    greenPotential O' μ (f x) = greenPotential O (μ.map g) x := by
  unfold greenPotential
  rw [integral_map hg.aemeasurable (measurable_greenFunction hO x).aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall (hgreen x))

end HarmonicBalls.Section6
