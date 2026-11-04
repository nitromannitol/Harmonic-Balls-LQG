import HarmonicBalls.Proofs.Sec6.RecurrenceFubini

/-! # Smooth annuli and their interior circles -/

namespace HarmonicBalls.Section6
open MeasureTheory Metric Set
open scoped ContDiff

/-- A polynomial defining function for a concentric annulus. -/
noncomputable def annulusDefiningFunction (c : ℂ) (r R : ℝ) (z : ℂ) : ℝ :=
  (‖z - c‖ ^ 2 - r ^ 2) * (‖z - c‖ ^ 2 - R ^ 2)

/-- Radial derivative of the defining function. -/
theorem fderiv_annulusDefiningFunction_radial (c z : ℂ) (r R : ℝ) :
    fderiv ℝ (annulusDefiningFunction c r R) z (z - c) =
      2 * ‖z - c‖ ^ 2 * ((‖z - c‖ ^ 2 - r ^ 2) + (‖z - c‖ ^ 2 - R ^ 2)) := by
  have hn : HasFDerivAt (fun z : ℂ => ‖z - c‖ ^ 2)
      (2 • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ ℂ)) z :=
    ((hasFDerivAt_id z).sub_const c).norm_sq
  have h := (hn.sub_const (r ^ 2)).mul (hn.sub_const (R ^ 2))
  have hd : fderiv ℝ (annulusDefiningFunction c r R) z = _ := h.fderiv
  rw [hd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
    innerSL_apply_apply, inner_self_eq_norm_sq_to_K]
  norm_num
  ring

/-- Every annulus with strictly positive inner radius and larger outer radius is
a smooth bounded open set. -/
theorem isSmoothBoundedOpen_annulus (c : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    IsSmoothBoundedOpen {z : ℂ | r < ‖z - c‖ ∧ ‖z - c‖ < R} := by
  have hR : 0 < R := hr.trans hrR
  have hsq : r ^ 2 < R ^ 2 := by nlinarith
  refine ⟨(Metric.isBounded_ball (x := c) (r := R)).subset ?_, annulusDefiningFunction c r R, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [Metric.mem_ball, dist_eq_norm] using hz.2
  · unfold annulusDefiningFunction
    exact (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const).mul
      (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).sub contDiff_const)
  · ext z
    simp only [mem_ofPred_eq, annulusDefiningFunction]
    have hn := norm_nonneg (z - c)
    constructor
    · rintro ⟨h1, h2⟩
      have hp : 0 < ‖z - c‖ ^ 2 - r ^ 2 := by nlinarith
      have hn' : ‖z - c‖ ^ 2 - R ^ 2 < 0 := by nlinarith
      exact mul_neg_of_pos_of_neg hp hn'
    · intro h
      rcases mul_neg_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · constructor <;> nlinarith [sq_nonneg (‖z - c‖ - r), sq_nonneg (‖z - c‖ - R)]
      · nlinarith [sq_nonneg (‖z - c‖ - r), sq_nonneg (‖z - c‖ - R)]
  · intro z hz hzero
    have hfactor : ‖z - c‖ ^ 2 - r ^ 2 = 0 ∨ ‖z - c‖ ^ 2 - R ^ 2 = 0 := by
      apply mul_eq_zero.mp
      exact hz
    have hq : 0 < ‖z - c‖ ^ 2 := by
      rcases hfactor with h | h <;> nlinarith [sq_pos_of_pos hr, sq_pos_of_pos hR]
    have hsum : (‖z - c‖ ^ 2 - r ^ 2) + (‖z - c‖ ^ 2 - R ^ 2) ≠ 0 := by
      rcases hfactor with h | h <;> nlinarith
    have hd := congrArg (fun L : ℂ →L[ℝ] ℝ => L (z - c)) hzero
    simp only [zero_apply] at hd
    rw [fderiv_annulusDefiningFunction_radial] at hd
    exact (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt hq)) hsum) hd

/-- The annulus and circle used in the fine-support argument. -/
noncomputable def fineSupportAnnulus (c : ℂ) (r : ℝ) : Set ℂ :=
  {z | r / 8 < ‖z - c‖ ∧ ‖z - c‖ < r}

/-- The fine-support annulus is smooth and contains its compact interior circle. -/
theorem fineSupportAnnulus_geometry (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSmoothBoundedOpen (fineSupportAnnulus c r) ∧
    IsCompact (sphere c (r / 4)) ∧ (sphere c (r / 4)).Nonempty ∧
    sphere c (r / 4) ⊆ fineSupportAnnulus c r ∧
    ∃ R : ℝ, 0 < R ∧ fineSupportAnnulus c r ⊆ ball 0 R := by
  refine ⟨isSmoothBoundedOpen_annulus c (by linarith) (by linarith),
    isCompact_sphere _ _, ?_, ?_, ‖c‖ + r + 1, by positivity, ?_⟩
  · refine ⟨c + ((r / 4 : ℝ) : ℂ), ?_⟩
    simp only [mem_sphere, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < r / 4)]
  · intro z hz
    have hz' : ‖z - c‖ = r / 4 := by
      simpa only [mem_sphere, dist_eq_norm] using hz
    simp only [fineSupportAnnulus, mem_ofPred_eq]
    constructor <;> linarith
  · intro z hz
    have hz' : ‖z - c‖ < r := hz.2
    have hzbound : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
      calc ‖z‖ = ‖(z - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
    simp only [mem_ball, dist_zero_right]
    linarith

universe u

/-- The fine-support Green-potential ratios are positive simultaneously for every
centre and every positive radius. -/
theorem ae_fineSupport_ratio_pos
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      0 < greenPotentialExtremaRatio (fineSupportAnnulus c r) (sphere c (r / 4)) (μ sample) := by
  filter_upwards [ae_lqg_greenPotential_extrema_ratio_pos hholder hfull hgrowth
    hγ hγ2 hα hGFF hμ hnonatom] with sample hω
  intro c r hr
  obtain ⟨ho, hk, hkne, hko, R, hR, hOR⟩ := fineSupportAnnulus_geometry c hr
  simpa only [greenPotentialExtremaRatio] using
    hω (fineSupportAnnulus c r) ho R hR hOR (sphere c (r / 4)) hk hkne hko

/-- A fine-support ratio at a fixed centre and radius is almost everywhere
measurable under LQG locality and Green-potential Hölder regularity. -/
theorem aemeasurable_fineSupport_ratio
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    AEMeasurable (fun sample =>
      greenPotentialExtremaRatio (fineSupportAnnulus c r) (sphere c (r / 4)) (μ sample)) P := by
  obtain ⟨ho, _, _, hko, _⟩ := fineSupportAnnulus_geometry c hr
  simpa only [greenPotentialExtremaRatio] using
    aemeasurable_lqg_greenPotential_ratio_of_locality hholder hγ hγ2 hα hGFF hμ hloc
      ho (hko.trans subset_closure)

/-- The geometric scales used in the fine-support argument. -/
noncomputable def fineSupportScale (n : ℕ) : ℝ := ((7 : ℝ)⁻¹) ^ n

/-- At every fixed centre, identical lower tails give positive recurrence of
fine-support ratios at geometric scales. -/
theorem ae_fineSupport_ratio_recurs_of_equal_lower_tails
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (c : ℂ)
    (hlaw : ∀ n a, P {sample | greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ sample) < a} =
      P {sample | greenPotentialExtremaRatio (fineSupportAnnulus c 1) (sphere c (1 / 4)) (μ sample) < a}) :
    ∀ᵐ sample ∂P, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ sample) := by
  let X : ℕ → Ω → ℝ := fun n sample =>
    greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
      (sphere c (fineSupportScale n / 4)) (μ sample)
  have h0 : fineSupportScale 0 = 1 := by simp [fineSupportScale]
  have hm : AEMeasurable (X 0) P := by
    simpa only [X, h0] using
      aemeasurable_fineSupport_ratio hholder hγ hγ2 hα hGFF hμ hloc c (by norm_num : (0 : ℝ) < 1)
  have hp : ∀ᵐ sample ∂P, 0 < X 0 sample := by
    filter_upwards [ae_fineSupport_ratio_pos hholder hfull hgrowth hγ hγ2 hα hGFF hμ hnonatom] with sample hs
    simpa only [X, h0] using hs c 1 (by norm_num)
  have hl : ∀ n a, P {sample | X n sample < a} = P {sample | X 0 sample < a} := by
    simpa only [X, h0] using hlaw
  exact ae_frequently_pos_of_equal_lower_tails_of_aemeasurable P X hm hp hl

/-- Jointly almost-everywhere measurable fine-support ratios with identical lower
tails recur positively simultaneously for Lebesgue-almost every centre. -/
theorem ae_ae_fineSupport_ratio_recurs_of_equal_lower_tails
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (hjoint : ∀ n, AEMeasurable (fun p : Ω × ℂ =>
      greenPotentialExtremaRatio (fineSupportAnnulus p.2 (fineSupportScale n))
        (sphere p.2 (fineSupportScale n / 4)) (μ p.1)) (P.prod volume))
    (hlaw : ∀ᵐ c ∂(volume : Measure ℂ), ∀ n a,
      P {sample | greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ sample) < a} =
      P {sample | greenPotentialExtremaRatio (fineSupportAnnulus c 1) (sphere c (1 / 4)) (μ sample) < a}) :
    ∀ᵐ sample ∂P, ∀ᵐ c ∂(volume : Measure ℂ), ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ sample) := by
  let X : ℕ → Ω × ℂ → ℝ := fun n p =>
    greenPotentialExtremaRatio (fineSupportAnnulus p.2 (fineSupportScale n))
      (sphere p.2 (fineSupportScale n / 4)) (μ p.1)
  have h0 : fineSupportScale 0 = 1 := by simp [fineSupportScale]
  have hp : ∀ᵐ c ∂(volume : Measure ℂ), ∀ᵐ sample ∂P, 0 < X 0 (sample, c) := by
    filter_upwards [] with c
    filter_upwards [ae_fineSupport_ratio_pos hholder hfull hgrowth hγ hγ2 hα hGFF hμ hnonatom] with sample hs
    simpa only [X, h0] using hs c 1 (by norm_num)
  have hl : ∀ᵐ c ∂(volume : Measure ℂ), ∀ n a,
      P {sample | X n (sample, c) < a} = P {sample | X 0 (sample, c) < a} := by
    simpa only [X, h0] using hlaw
  exact ae_ae_frequently_pos_of_equal_lower_tails_of_aemeasurable P volume X hjoint hp hl

end HarmonicBalls.Section6
