import HarmonicBalls.Proofs.Sec6.VeryGoodAnnulusSizeLocality
import HarmonicBalls.Proofs.Sec6.AnnularNormalizedRestriction
import HarmonicBalls.Proofs.Sec6.LogAnnulusHitting
import HarmonicBalls.Proofs.Sec8.VeryGoodMeasureVersion

/-! # Borel representation on a size annulus

The imported locality development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal

universe u

/-- A Borel representative works for atomless, locally finite measures with
full support inside the size annulus, without requiring mass outside it. -/
theorem exists_measurable_isVeryGoodAnnulus_on_size_annulus
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ μ : Measure ℂ,
      (∀ x : ℂ, μ {x} = 0) → IsLocallyFiniteMeasure μ →
      (∀ U : Set ℂ, IsOpen U → U.Nonempty → U ⊆ annulus 0 (ρ / 4) (2 * ρ) → 0 < μ U) →
      (μ ∈ G ↔ IsVeryGoodAnnulus μ βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃) := by
  let A : Set ℂ := annulus 0 (ρ / 4) (2 * ρ)
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  let F : Measure ℂ → Measure ℂ := fun μ => μ.restrict A + volume.restrict Aᶜ
  have hFm : Measurable F := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    simp only [F, Measure.add_apply, Measure.restrict_apply hU]
    exact (Measure.measurable_coe (hU.inter hAo.measurableSet)).add measurable_const
  obtain ⟨H, hHm, hH⟩ := exists_measurable_isVeryGoodAnnulus_on_fullSupport
    βminus ρ hρ N₀ a b C₁m C₁p C₂m C₂p C₃ ha hpolar
  refine ⟨F ⁻¹' H, hHm.preimage hFm, ?_⟩
  intro μ hatom hloc hlocal
  let : IsLocallyFiniteMeasure μ := hloc
  have hFa : ∀ x : ℂ, F μ {x} = 0 := by
    intro x
    have h1 : μ.restrict A {x} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton x)]
      exact measure_mono_null inter_subset_left (hatom x)
    have h2 : (volume.restrict Aᶜ : Measure ℂ) {x} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton x)]
      exact measure_mono_null inter_subset_left (measure_singleton x)
    simp only [F, Measure.add_apply, h1, h2, add_zero]
  have hFl : IsLocallyFiniteMeasure (F μ) := by
    refine ⟨fun x => ⟨ball x 1, isOpen_ball.mem_nhds (mem_ball_self (by norm_num)), ?_⟩⟩
    change (μ.restrict A + (volume.restrict Aᶜ : Measure ℂ)) (ball x 1) < ∞
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨
      (Measure.restrict_apply_le A _).trans_lt (lt_top_iff_ne_top.mpr measure_ball_ne_top),
      (Measure.restrict_apply_le Aᶜ _).trans_lt (lt_top_iff_ne_top.mpr measure_ball_ne_top)⟩
  have hFfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < F μ U := by
    intro U hU hUne
    by_cases hUA : (U ∩ A).Nonempty
    · have hp := hlocal (U ∩ A) (hU.inter hAo) hUA inter_subset_right
      have hp' : 0 < μ.restrict A U := by
        rw [Measure.restrict_apply hU.measurableSet]
        exact hp
      change 0 < μ.restrict A U + (volume.restrict Aᶜ : Measure ℂ) U
      exact lt_of_lt_of_le hp' (le_add_of_nonneg_right (zero_le))
    · have hsub : U ⊆ Aᶜ := by
        intro x hx hxA
        exact hUA ⟨x, hx, hxA⟩
      have hp : 0 < (volume : Measure ℂ) U := hU.measure_pos volume hUne
      have hp' : 0 < (volume.restrict Aᶜ : Measure ℂ) U := by
        rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.mpr hsub]
        exact hp
      change 0 < μ.restrict A U + (volume.restrict Aᶜ : Measure ℂ) U
      exact lt_of_lt_of_le hp' (le_add_of_nonneg_left (zero_le))
  have hFA : (F μ).restrict A = μ.restrict A := by
    simp only [F, Measure.restrict_add, Measure.restrict_restrict hAo.measurableSet,
      inter_self, inter_compl_self, Measure.restrict_empty, add_zero]
  change (F μ ∈ H ↔ _)
  rw [hH (F μ) hFa hFl hFfull,
    ← isVeryGoodAnnulus_restrict_size_annulus (F μ) βminus ρ 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ hρ hN₀,
    hFA, isVeryGoodAnnulus_restrict_size_annulus μ βminus ρ 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ hρ hN₀]

/-- A local normalized-measure version gives modulo-constant field locality
of the very-good event at the origin. -/
theorem isFieldMeasurableModConst_veryGoodAnnulus_of_normalized_version
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (μ : Ω → Measure ℂ)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀)
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
      {ω | IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃} := by
  let A : Set ℂ := annulus 0 (ρ / 4) (2 * ρ)
  obtain ⟨ν, hν, hνeq⟩ := hversion
  obtain ⟨G, hG, hrep⟩ := exists_measurable_isVeryGoodAnnulus_on_size_annulus
    βminus ρ hρ N₀ hN₀ a b C₁m C₁p C₂m C₂p C₃ ha hpolar
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
  change IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ = (ν ω ∈ G)
  rw [heq]
  exact propext ((hequiv.trans (isVeryGoodAnnulus_normalizedRestriction_size_annulus
    (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ hρ hN₀ hp.ne' hf)).symm)

/-- Under full support and the staged affine laws, a very-good annulus at the
origin is local modulo constants, given nonatomicity and Brownian point
avoidance. -/
theorem isFieldMeasurableModConst_veryGoodAnnulus_zero_of_affine
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    IsFieldMeasurableModConst P 0 hC (annulus 0 (ρ / 4) (2 * ρ))
      {ω | IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃} := by
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hversion := IsWholePlaneGFF.exists_modConst_annular_normalizedRestriction_of_affine
    hfull hgff hμ hAff hCC hγ hγ2 hQ 0 (show 0 < ρ / 4 by positivity)
      (show ρ / 4 < 2 * ρ by linarith)
  apply isFieldMeasurableModConst_veryGoodAnnulus_of_normalized_version P hC μ
    βminus ρ hρ N₀ hN₀ a b C₁m C₁p C₂m C₂p C₃ ha hversion hatom
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
theorem isFieldMeasurableModConst_veryGoodAnnulus_zero
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2)
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hatom : ∀ᵐ ω ∂P, ∀ x : ℂ, μ ω {x} = 0) :
    IsFieldMeasurableModConst P 0 hC (annulus 0 (ρ / 4) (2 * ρ))
      {ω | IsVeryGoodAnnulus (μ ω) βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃} := by
  apply isFieldMeasurableModConst_veryGoodAnnulus_zero_of_affine hfull hgff hμ hAff hCC
    hγ hγ2 βminus ρ hρ N₀ hN₀ a b C₁m C₁p C₂m C₂p C₃ ha hatom
  intro u x hxu
  exact planarBrownianMotion_point_avoidance u x hxu.symm

end HarmonicBalls.Section6
