import HarmonicBalls.Proofs.Sec6.PhaseVeryGoodFieldLocality
import HarmonicBalls.Proofs.Sec6.RecenteredLocalityTranslation

/-! # Recentered very-good annulus locality from translation

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`. The phase records the
translation of the absolute lattice.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal

universe u

/-- The absolute-lattice event at a deterministic center is local in the
recentered field, with its lattice phase preserved by translation. -/
theorem isFieldMeasurableModConst_veryGoodAnnulus_recentered_of_translation
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
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
    isLQGMeasureOfField_translate hgff hμ z
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν, hνeq⟩ := exists_modConst_recentered_annular_normalizedRestriction_of_translation
    hfull hgff hμ hAff hγ hγ2 z (show 0 < ρ / 4 by positivity)
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
