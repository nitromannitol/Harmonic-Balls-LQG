import HarmonicBalls.Proofs.Sec6.AnnulusGeometry
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Laws of Green-potential extrema ratios

The law of a random measure determines the law of its potential ratio whenever
both potentials are almost surely continuous on the sets used for the extrema.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory

/-- Equal laws of random measures transfer to Green-potential ratios if the
potential is almost surely continuous on the sets defining the extrema. -/
theorem identDistrib_greenPotentialExtremaRatio
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ ν : Ω → Measure ℂ} (hd : IdentDistrib μ ν P P)
    {O K : Set ℂ} (hO : IsOpen O) (hb : Bornology.IsBounded O)
    (hcμ : ∀ᵐ ω ∂P, Continuous (fun z : K => greenPotential O (μ ω) z) ∧
      Continuous (fun z : O => greenPotential O (μ ω) z))
    (hcν : ∀ᵐ ω ∂P, Continuous (fun z : K => greenPotential O (ν ω) z) ∧
      Continuous (fun z : O => greenPotential O (ν ω) z)) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio O K (μ ω))
      (fun ω => greenPotentialExtremaRatio O K (ν ω)) P P := by
  classical
  obtain ⟨J, hJ, dJ⟩ := TopologicalSpace.exists_countable_dense K
  obtain ⟨L, hL, dL⟩ := TopologicalSpace.exists_countable_dense O
  have : Countable J := hJ.to_subtype
  have : Countable L := hL.to_subtype
  let F : Measure ℂ → ℝ := fun m =>
    ((⨅ z : J, ENNReal.ofReal (greenPotential O m z.1)) /
      (⨆ z : L, ENNReal.ofReal (greenPotential O m z.1))).toReal
  have hF : Measurable F := by
    apply ENNReal.measurable_toReal.comp
    apply Measurable.div
    · exact Measurable.iInf fun z => ENNReal.measurable_ofReal.comp
        (measurable_greenPotential_measure hO hb z.1)
    · exact Measurable.iSup fun z => ENNReal.measurable_ofReal.comp
        (measurable_greenPotential_measure hO hb z.1)
  have heq (m : Measure ℂ)
      (hcont : Continuous (fun z : K => greenPotential O m z) ∧
        Continuous (fun z : O => greenPotential O m z)) :
      F m = greenPotentialExtremaRatio O K m := by
    have hi : (⨅ z : J, ENNReal.ofReal (greenPotential O m z.1)) =
        ⨅ z : K, ENNReal.ofReal (greenPotential O m z) := by
      simpa only [Function.comp_apply] using
        dJ.ciInf (ENNReal.continuous_ofReal.comp hcont.1) (OrderBot.bddBelow _)
    have hs : (⨆ z : L, ENNReal.ofReal (greenPotential O m z.1)) =
        ⨆ z : O, ENNReal.ofReal (greenPotential O m z) := by
      simpa only [Function.comp_apply] using
        dL.ciSup (ENNReal.continuous_ofReal.comp hcont.2) (OrderTop.bddAbove _)
    simp only [F, greenPotentialExtremaRatio, hi, hs]
  have hfμ : (F ∘ μ) =ᵐ[P] fun ω => greenPotentialExtremaRatio O K (μ ω) := by
    filter_upwards [hcμ] with ω hω
    exact heq _ hω
  have hfν : (F ∘ ν) =ᵐ[P] fun ω => greenPotentialExtremaRatio O K (ν ω) := by
    filter_upwards [hcν] with ω hω
    exact heq _ hω
  have hFdist := hd.comp hF
  exact ((IdentDistrib.of_ae_eq hFdist.aemeasurable_fst hfμ).symm.trans hFdist).trans
    (IdentDistrib.of_ae_eq hFdist.aemeasurable_snd hfν)

universe u

/-- LQG Green potentials are almost surely continuous on the two sets used
for a ratio. -/
theorem ae_continuous_lqg_greenPotential_extrema
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {O K : Set ℂ} (hO : IsSmoothBoundedOpen O) (hK : K ⊆ closure O) :
    ∀ᵐ ω ∂P, Continuous (fun z : K => greenPotential O (μ ω) z) ∧
      Continuous (fun z : O => greenPotential O (μ ω) z) := by
  filter_upwards [hholder γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hhold
  obtain ⟨_, C, r, hr, hcont⟩ := hhold O hO (fun _ => 1) (memLp_top_const (1 : ℝ))
  have hcont' : ContinuousOn (greenPotential O (μ ω)) (closure O) := by
    apply greenPotential_continuousOn_of_holder (μ ω)
    refine ⟨C, r, hr, ?_⟩
    simpa only [mul_one] using hcont
  exact ⟨(hcont'.mono hK).domRestrict, (hcont'.mono subset_closure).domRestrict⟩

/-- For a fixed smooth domain, normalized dilations of an LQG measure give
identically distributed potential ratios. The affine invariance and coordinate
change inputs are staged assumptions. -/
theorem identDistrib_lqg_greenPotentialExtremaRatio_normalizedPullback
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    {k : ℝ} (hk : 0 < k) {O K : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hK : K ⊆ closure O) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio O K (μ ω))
      (fun ω => greenPotentialExtremaRatio O K
        (normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω))) P P := by
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  have hs := hAff hGFF (k : ℂ) (by exact_mod_cast hk.ne') 0
  have hsμ := isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ hk
  have hsμ' : IsLQGMeasureOfField P γ α₀
      (fun ω r z => hcirc ω (‖(k : ℂ)‖ * r) ((k : ℂ) * z + 0) - hcirc ω ‖(k : ℂ)‖ 0)
      (fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)) := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk, add_zero,
      Complex.real_smul] using hsμ
  exact identDistrib_greenPotentialExtremaRatio
    (hGFF.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk) hopen hO.1
    (ae_continuous_lqg_greenPotential_extrema hholder hγ hγ2 hα hGFF hμ hO hK)
    (ae_continuous_lqg_greenPotential_extrema hholder hγ hγ2 hα hs hsμ' hO hK)

/-- The normalization constant cancels: a pulled-back LQG measure has the
same fixed-domain potential-ratio law as the original measure. -/
theorem identDistrib_lqg_greenPotentialExtremaRatio_pullback
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    {k : ℝ} (hk : 0 < k) {O K : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hK : K ⊆ closure O) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio O K (μ ω))
      (fun ω => greenPotentialExtremaRatio O K
        ((μ ω).map (fun x : ℂ => k⁻¹ • x))) P P := by
  have hd := identDistrib_lqg_greenPotentialExtremaRatio_normalizedPullback
    hholder hγ hγ2 hα hGFF hμ hAff hCC hk hO hK
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  simp only [normalizedPullbackMeasure, greenPotentialExtremaRatio]
  apply greenPotential_extrema_ratio_smul_measure
  · apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    positivity
  · exact ENNReal.ofReal_ne_top

/-- Fixed fine-support ratios are almost everywhere measurable from the GFF
and LQG measure definitions and Green-potential regularity. -/
theorem aemeasurable_fineSupport_ratio_of_gff
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun ω =>
      greenPotentialExtremaRatio (fineSupportAnnulus c r) (Metric.sphere c (r / 4)) (μ ω)) P := by
  obtain ⟨ho, _, _, hko, _⟩ := fineSupportAnnulus_geometry c hr
  have heval : ∀ A : Set ℂ, MeasurableSet A → AEMeasurable (fun ω => μ ω A) P := by
    intro A hA
    exact (Measure.measurable_coe hA).comp_aemeasurable (hGFF.aemeasurable_lqgMeasure hμ)
  simpa only [greenPotentialExtremaRatio] using
    aemeasurable_lqg_greenPotential_ratio_of_evaluations hholder hγ hγ2 hα hGFF hμ heval
      ho (hko.trans subset_closure)

/-- Equal lower tails yield fine-support recurrence at a fixed centre without
an additional locality assumption. -/
theorem ae_fineSupport_ratio_recurs_of_equal_lower_tails_of_gff
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc) (c : ℂ)
    (hlaw : ∀ n a, P {ω | greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (Metric.sphere c (fineSupportScale n / 4)) (μ ω) < a} =
      P {ω | greenPotentialExtremaRatio (fineSupportAnnulus c 1) (Metric.sphere c (1 / 4)) (μ ω) < a}) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (Metric.sphere c (fineSupportScale n / 4)) (μ ω) := by
  let X : ℕ → Ω → ℝ := fun n ω => greenPotentialExtremaRatio
    (fineSupportAnnulus c (fineSupportScale n)) (Metric.sphere c (fineSupportScale n / 4)) (μ ω)
  have h0 : fineSupportScale 0 = 1 := by simp [fineSupportScale]
  have hm : AEMeasurable (X 0) P := by
    simpa only [X, h0] using
      aemeasurable_fineSupport_ratio_of_gff hholder hγ hγ2 hα hGFF hμ c (by norm_num : (0 : ℝ) < 1)
  have hp : ∀ᵐ ω ∂P, 0 < X 0 ω := by
    filter_upwards [ae_fineSupport_ratio_pos hholder hfull hgrowth hγ hγ2 hα hGFF hμ hnonatom] with ω hω
    simpa only [X, h0] using hω c 1 (by norm_num)
  apply ae_frequently_pos_of_equal_lower_tails_of_aemeasurable P X hm hp
  intro n a
  simpa only [X, h0] using hlaw n a

end HarmonicBalls.Section6
