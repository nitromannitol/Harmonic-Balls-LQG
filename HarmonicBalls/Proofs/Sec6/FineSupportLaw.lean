import HarmonicBalls.Proofs.Sec6.GreenDilation

/-! # Affine laws for fine-support annuli -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter Topology

/-- A fine-support annulus is the positive affine image of the unit annulus. -/
theorem fineSupportAnnulus_affine (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun z : ℂ => r • z + c) '' fineSupportAnnulus 0 1 = fineSupportAnnulus c r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    change (1 : ℝ) / 8 < ‖w - 0‖ ∧ ‖w - 0‖ < 1 at hw
    change r / 8 < ‖r • w + c - c‖ ∧ ‖r • w + c - c‖ < r
    simp only [sub_zero] at hw
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    constructor <;> nlinarith
  · intro hz
    change r / 8 < ‖z - c‖ ∧ ‖z - c‖ < r at hz
    refine ⟨r⁻¹ • (z - c), ?_, ?_⟩
    · change (1 : ℝ) / 8 < ‖r⁻¹ • (z - c) - 0‖ ∧ ‖r⁻¹ • (z - c) - 0‖ < 1
      rw [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      rw [show r⁻¹ * ‖z - c‖ = ‖z - c‖ / r by rw [div_eq_mul_inv, mul_comm],
        lt_div_iff₀ hr, div_lt_iff₀ hr]
      constructor <;> nlinarith
    · simp only [smul_inv_smul₀ hr.ne', sub_add_cancel]

/-- The interior circle is the corresponding affine image of the unit circle. -/
theorem fineSupportSphere_affine (c : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun z : ℂ => r • z + c) '' sphere 0 (1 / 4) = sphere c (r / 4) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [mem_sphere, dist_eq_norm, sub_zero] at hw
    simp only [mem_sphere, dist_eq_norm, add_sub_cancel_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, hw]
    ring
  · intro hz
    simp only [mem_sphere, dist_eq_norm] at hz
    refine ⟨r⁻¹ • (z - c), ?_, ?_⟩
    · simp only [mem_sphere, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr), hz]
      field_simp
    · simp only [smul_inv_smul₀ hr.ne', sub_add_cancel]

universe u

/-- The fine-support ratio has the same law at every centre and positive scale. -/
theorem identDistrib_fineSupport_ratio
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IdentDistrib (fun ω => greenPotentialExtremaRatio (fineSupportAnnulus 0 1)
        (sphere 0 (1 / 4)) (μ ω))
      (fun ω => greenPotentialExtremaRatio (fineSupportAnnulus c r)
        (sphere c (r / 4)) (μ ω)) P P := by
  obtain ⟨ho, _, _, hko, _⟩ := fineSupportAnnulus_geometry 0 (by norm_num : (0 : ℝ) < 1)
  have hd := identDistrib_lqg_greenPotentialExtremaRatio_positive_affine
    hholder hγ hγ2 h hμ hAff hCC hr c ho (hko.trans subset_closure)
  simpa only [fineSupportAnnulus_affine c hr, fineSupportSphere_affine c hr] using hd

/-- The lower tails of fine-support ratios are independent of the centre and
positive scale. -/
theorem fineSupport_ratio_lower_tail_eq
    (hholder : GreenPotentialHolderStmt.{u}) {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (c d : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (a : ℝ) :
    P {ω | greenPotentialExtremaRatio (fineSupportAnnulus c r) (sphere c (r / 4)) (μ ω) < a} =
    P {ω | greenPotentialExtremaRatio (fineSupportAnnulus d s) (sphere d (s / 4)) (μ ω) < a} := by
  have hcr := identDistrib_fineSupport_ratio hholder hγ hγ2 h hμ hAff hCC c hr
  have hds := identDistrib_fineSupport_ratio hholder hγ hγ2 h hμ hAff hCC d hs
  exact (hcr.symm.trans hds).measure_mem_eq measurableSet_Iio

/-- At each fixed centre, fine-support ratios recur above a positive threshold. -/
theorem ae_fineSupport_ratio_recurs_of_gff
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc) (c : ℂ) :
    ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ ω) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  apply ae_fineSupport_ratio_recurs_of_equal_lower_tails_of_gff
    hholder hfull hgrowth hγ hγ2 hQ h hμ hnonatom c
  intro n a
  exact fineSupport_ratio_lower_tail_eq hholder hγ hγ2 h hμ hAff hCC c c
    (by unfold fineSupportScale; positivity) (by norm_num) a

/-- Joint measurability upgrades fixed-centre recurrence to almost every centre. -/
theorem ae_ae_fineSupport_ratio_recurs_of_gff
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ 0 hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hjoint : ∀ n, AEMeasurable (fun p : Ω × ℂ =>
      greenPotentialExtremaRatio (fineSupportAnnulus p.2 (fineSupportScale n))
        (sphere p.2 (fineSupportScale n / 4)) (μ p.1)) (P.prod volume)) :
    ∀ᵐ ω ∂P, ∀ᵐ c ∂(volume : Measure ℂ), ∃ a : ℝ, 0 < a ∧ ∀ N : ℕ, ∃ n ≥ N,
      a ≤ greenPotentialExtremaRatio (fineSupportAnnulus c (fineSupportScale n))
        (sphere c (fineSupportScale n / 4)) (μ ω) := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  apply ae_ae_fineSupport_ratio_recurs_of_equal_lower_tails
    hholder hfull hgrowth hγ hγ2 hQ h hμ hnonatom hjoint
  filter_upwards [] with c n a
  exact fineSupport_ratio_lower_tail_eq hholder hγ hγ2 h hμ hAff hCC c c
    (by unfold fineSupportScale; positivity) (by norm_num) a

end HarmonicBalls.Section6
