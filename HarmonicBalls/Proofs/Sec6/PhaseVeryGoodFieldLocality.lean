import HarmonicBalls.Proofs.Sec6.PhaseVeryGoodSizeBorel
import HarmonicBalls.Proofs.Sec6.RecenteredAnnularNormalizedRestriction

/-! # Fixed-phase field locality

The imported annulus iteration uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal

universe u

/-- A local normalized-measure version gives modulo-constant field locality
of the very-good event at the origin. -/
theorem isFieldMeasurableModConst_phaseVeryGoodAnnulus_of_normalized_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (μ : Ω → Measure ℂ)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (phase : ℂ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hversion : ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (fieldSigmaAlgebraModConst 0 hC (annulus 0 (ρ / 4) (2 * ρ))) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (annulus 0 (ρ / 4) (2 * ρ)))
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 (ρ / 4) (2 * ρ)))
    (hlocal : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty →
      U ⊆ annulus 0 (ρ / 4) (2 * ρ) → 0 < μ ω U)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IsFieldMeasurableModConst P 0 hC (annulus 0 (ρ / 4) (2 * ρ))
      {ω | PhaseVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase} := by
  let A : Set ℂ := annulus 0 (ρ / 4) (2 * ρ)
  obtain ⟨ν, hν, hνeq⟩ := hversion
  obtain ⟨G, hG, hrep⟩ := exists_measurable_phaseVeryGoodAnnulus_on_size_annulus
    βminus ρ hρ N₀ hN₀ phase a b C₁m C₁p C₂m C₂p C₃ ha hpolar
  refine ⟨ν ⁻¹' G, hν hG, ?_⟩
  filter_upwards [hνeq, hatom, hfinite, hpositive, hlocal] with ω heq hat hf hp hloc
  have hnatom : ∀ x : ℂ, normalizedRestriction (μ ω) A {x} = 0 := by
    intro x
    rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
    have hz : μ ω ({x} ∩ A) = 0 := measure_mono_null inter_subset_left (hat x)
    simp only [hz, smul_zero]
  have hnprob : IsProbabilityMeasure (normalizedRestriction (μ ω) A) := by
    refine ⟨?_⟩
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hp.ne' hf
  have hnloc : IsLocallyFiniteMeasure (normalizedRestriction (μ ω) A) := by
    let : IsProbabilityMeasure (normalizedRestriction (μ ω) A) := hnprob
    infer_instance
  have hnfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → U ⊆ A →
      0 < normalizedRestriction (μ ω) A U := by
    intro U hU hUne hsub
    rw [normalizedRestriction, Measure.smul_apply, Measure.restrict_apply hU.measurableSet,
      inter_eq_left.mpr hsub]
    exact ENNReal.mul_pos (ENNReal.inv_ne_zero.mpr hf) (hloc U hU hUne hsub).ne'
  have hequiv := hrep (normalizedRestriction (μ ω) A) hnatom hnloc hnfull
  change PhaseVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase = (ν ω ∈ G)
  rw [heq]
  exact propext ((hequiv.trans (phaseVeryGoodAnnulus_normalizedRestriction_size_annulus
    (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase hρ hN₀ hp.ne' hf)).symm)

/-- Under full support and the staged affine laws, a very-good annulus at the
origin is local modulo constants, given nonatomicity and Brownian point
avoidance. -/
theorem isFieldMeasurableModConst_phaseVeryGoodAnnulus_zero_of_affine
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (phase : ℂ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IsFieldMeasurableModConst P 0 hC (annulus 0 (ρ / 4) (2 * ρ))
      {ω | PhaseVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase} := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hversion := IsWholePlaneGFF.exists_modConst_annular_normalizedRestriction_of_affine
    hfull hgff hμ hAff hCC hγ hγ2 hQ 0 (show 0 < ρ / 4 by positivity)
      (show ρ / 4 < 2 * ρ by linarith)
  apply isFieldMeasurableModConst_phaseVeryGoodAnnulus_of_normalized_version P hC μ
    βminus ρ hρ N₀ hN₀ phase a b C₁m C₁p C₂m C₂p C₃ ha hversion hatom
  · filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset)
  · filter_upwards [hfull γ 0 hγ hγ2 hQ Ω P hC hcirc μ hgff hμ] with ω hω
    exact hω _ (isOpen_ball.sdiff isClosed_closedBall) (size_annulus_nonempty hρ)
  · filter_upwards [hfull γ 0 hγ hγ2 hQ Ω P hC hcirc μ hgff hμ] with ω hω U hU hUne _
    exact hω U hU hUne
  · exact hpolar

/-- Brownian point polarity removes the point-avoidance premise from the
origin locality result. -/
theorem isFieldMeasurableModConst_phaseVeryGoodAnnulus_zero
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (phase : ℂ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0) :
    IsFieldMeasurableModConst P 0 hC (annulus 0 (ρ / 4) (2 * ρ))
      {ω | PhaseVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase} := by
  apply isFieldMeasurableModConst_phaseVeryGoodAnnulus_zero_of_affine hfull hgff hμ hAff hCC
    hγ hγ2 βminus ρ hρ N₀ hN₀ phase a b C₁m C₁p C₂m C₂p C₃ ha hatom
  intro u x hxu
  exact planarBrownianMotion_point_avoidance u x hxu.symm

/-- The phase shift records exactly how translation moves the absolute lattice. -/
theorem phaseVeryGoodAnnulus_affineMeasure_translate
    {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (β ρ : ℝ) (z : ℂ) (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ω : Ω) :
    PhaseVeryGoodAnnulus (affineMeasure γ hcirc μ 1 z ω) β ρ 0 N
        a b C₁m C₁p C₂m C₂p C₃ (-z) ↔
      IsVeryGoodAnnulus (μ ω) β ρ z N a b C₁m C₁p C₂m C₂p C₃ := by
  unfold affineMeasure
  rw [phaseVeryGoodAnnulus_smul _ _ _ _ _ _ _ _ _ _ _ _ _
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))) ENNReal.ofReal_ne_top]
  simpa only [div_one, PhaseVeryGoodAnnulus] using
    (isVeryGoodAnnulus_iff_centered_shifted_phase (μ ω) β ρ z N
      a b C₁m C₁p C₂m C₂p C₃).symm

/-- The absolute-lattice event at a deterministic center is local in the
recentered field, with its lattice phase preserved by translation. -/
theorem isFieldMeasurableModConst_veryGoodAnnulus_recentered
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ)
    (β ρ : ℝ) (hρ : 0 < ρ) (N : ℕ) (hN : 9 ≤ N)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hatom : LQGMeasureNonatomic P γ 0 (affinePairing hC hcirc 1 z)
      (affineCircle hcirc 1 z)) :
    IsFieldMeasurableModConst P 0 (affinePairing hC hcirc 1 z)
      (annulus 0 (ρ / 4) (2 * ρ))
      {ω | IsVeryGoodAnnulus (μ ω) β ρ z N a b C₁m C₁p C₂m C₂p C₃} := by
  let η := affineMeasure γ hcirc μ 1 z
  have hs : IsWholePlaneGFF P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z) :=
    hAff hgff 1 one_ne_zero z
  have hη : IsLQGMeasureOfField P γ 0 (affineCircle hcirc 1 z) η :=
    isLQGMeasureOfField_affine hCC hgff hγ hγ2 hμ one_ne_zero z
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν, hνeq⟩ := exists_modConst_recentered_annular_normalizedRestriction
    hfull hgff hμ hAff hCC hγ hγ2 z (show 0 < ρ / 4 by positivity)
      (show ρ / 4 < 2 * ρ by linarith)
  have hversion : ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (fieldSigmaAlgebraModConst 0 (affinePairing hC hcirc 1 z)
          (annulus 0 (ρ / 4) (2 * ρ))) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (η ω) (annulus 0 (ρ / 4) (2 * ρ)) := by
    refine ⟨ν, hν, ?_⟩
    filter_upwards [hνeq] with ω hω
    rw [hω]
    dsimp only [η, affineMeasure]
    rw [normalizedRestriction_smul _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
      ENNReal.ofReal_ne_top]
    simp only [div_one]
  have hfinite : ∀ᵐ ω ∂P, η ω (annulus 0 (ρ / 4) (2 * ρ)) ≠ ∞ := by
    filter_upwards [hη] with ω hω
    let : IsLocallyFiniteMeasure (η ω) := hω.isLocallyFiniteMeasure
    exact ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset)
  have hfull' := hfull γ 0 hγ hγ2 hQ Ω P _ _ η hs hη
  have hpositive : ∀ᵐ ω ∂P, 0 < η ω (annulus 0 (ρ / 4) (2 * ρ)) := by
    filter_upwards [hfull'] with ω hω
    exact hω _ (isOpen_ball.sdiff isClosed_closedBall) (size_annulus_nonempty hρ)
  have hlocal : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty →
      U ⊆ annulus 0 (ρ / 4) (2 * ρ) → 0 < η ω U := by
    filter_upwards [hfull'] with ω hω U hU hUne _
    exact hω U hU hUne
  have hpol : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x := by
    intro u x hxu
    exact planarBrownianMotion_point_avoidance u x hxu.symm
  have hresult := isFieldMeasurableModConst_phaseVeryGoodAnnulus_of_normalized_version
    P (affinePairing hC hcirc 1 z) η β ρ hρ N hN (-z)
    a b C₁m C₁p C₂m C₂p C₃ ha hversion (hatom hs hγ hγ2 hQ η hη)
    hfinite hpositive hlocal hpol
  obtain ⟨A, hA, hAe⟩ := hresult
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAe] with ω hω
  simpa only [η, mem_ofPred_eq, phaseVeryGoodAnnulus_affineMeasure_translate] using hω

end HarmonicBalls.Section6
