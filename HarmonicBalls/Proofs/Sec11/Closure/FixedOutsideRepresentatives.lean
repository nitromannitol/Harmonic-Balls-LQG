import HarmonicBalls.Proofs.Sec11.Closure.FixedRawPositiveDerived
import HarmonicBalls.Proofs.Sec11.PinchOutsideFirstCertificate
import HarmonicBalls.Proofs.Sec11.PinchOutsideBaseMetric
import HarmonicBalls.Proofs.Sec11.PinchOutsideAnnulusMass
import HarmonicBalls.Proofs.Sec11.ExpectedLQGLocalBound
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-!
# Outside representatives of the fixed pinch configuration (Section 11, Lemma `l:r8-outside`)

Lean counterpart of Lemma `l:r8-outside` (`notes/sec11-proof/sec11-proof-r8.tex`, line 1057): the outside
observables of the fixed configuration have versions measurable for the pinned σ-algebra `fixedPinnedSigma hC`
(the σ-algebra of the zero-mean local pairings of the field on the outside of a neighbourhood of `W`), equal
almost surely to the original observables. The representatives are only almost surely equal to the original
functions; the consumers of this file therefore take almost-sure representatives, not exact measurability.

Inputs used here are the closed statements `exists_positive_outside_first_certificate`,
`exists_outside_baseMetric_sphere_distance`, `exists_outside_green_threshold` (Proofs/Sec11), and the
volume-zero argument for the frontier of the annulus `annulus 0 3 6`, which is the same argument as the square
frontier (`Proofs/Sec11/FixedSquareFrontierNull.lean`). No affine-invariance input is used.

Terminology: pinned σ-algebra and modulo constants (Armstrong-Kuusi-Mourrat, Duplantier-Sheffield); Green
potential of an annulus (Armitage-Gardiner).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Shrinking the index set of the zero-mean local pairings shrinks the modulo-constant σ-algebra. -/
theorem localModConstComap_le_of_subset {Ω : Type*} {α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ}
    {U V : Set ℂ} (hUV : U ⊆ V) :
    MeasurableSpace.comap (localModConstPairings α hC U) inferInstance ≤
      MeasurableSpace.comap (localModConstPairings α hC V) inferInstance := by
  let : MeasurableSpace Ω := MeasurableSpace.comap (localModConstPairings α hC V) inferInstance
  have hmeas : Measurable (localModConstPairings α hC U) := by
    refine measurable_pi_iff.2 (fun φ => ?_)
    obtain ⟨φ, hφ, hint⟩ := φ
    let hφV : LocalZeroMeanTest V := ⟨φ, ⟨⟨hφ.1, hφ.2.1, hφ.2.2.trans hUV⟩, hint⟩⟩
    exact (measurable_pi_apply hφV).comp (comap_measurable (localModConstPairings α hC V))
  exact measurable_iff_comap_le.1 hmeas

/-- The complement of the closed `4/100`-neighbourhood of the fixed `W` lies in the fixed outside set. -/
theorem compl_closure_fixedW_subset_fixedOutside : (closure fixedW)ᶜ ⊆ fixedOutside := by
  rw [fixedW, closure_ball _ (by norm_num), fixedOutside]
  exact compl_subset_compl.2 (closedBall_subset_closedBall (by norm_num))

/-- The outside pinned σ-algebra of the fixed configuration is contained in the pinned σ-algebra
`fixedPinnedSigma hC`. -/
theorem comap_localModConstPairings_outside_le_fixedPinnedSigma {Ω : Type} (hC : Ω → (ℂ → ℝ) → ℝ) :
    MeasurableSpace.comap (localModConstPairings 0 hC (closure fixedW)ᶜ) inferInstance ≤
      fixedPinnedSigma hC :=
  localModConstComap_le_of_subset compl_closure_fixedW_subset_fixedOutside

/-- The frontier of the annulus `annulus z r R` lies on its two bounding circles. -/
theorem frontier_annulus_subset_spheres (z : ℂ) (r R : ℝ) :
    frontier (annulus z r R) ⊆ sphere z R ∪ sphere z r := by
  have hsub := (frontier_inter_subset (ball z R) (closedBall z r)ᶜ).trans
    (union_subset_union inter_subset_left inter_subset_right)
  exact hsub.trans (union_subset_union frontier_ball_subset_sphere (by
    simpa only [frontier_compl] using (frontier_closedBall_subset_sphere (x := z) (ε := r))))

/-- The frontier of `annulus 0 3 6` has zero LQG mass almost surely (zero-charge measure). -/
theorem ae_lqgMeasure_frontier_annulus_zero_three_six_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, μ ω (frontier (annulus 0 3 6)) = 0 := by
  have hsub := frontier_annulus_subset_spheres (0 : ℂ) 3 6
  have hK : IsCompact (frontier (annulus (0 : ℂ) 3 6)) :=
    ((isCompact_sphere (0 : ℂ) 6).union (isCompact_sphere (0 : ℂ) 3)).of_isClosed_subset
      isClosed_frontier hsub
  have hvol : volume (frontier (annulus (0 : ℂ) 3 6)) = 0 :=
    measure_mono_null hsub (measure_union_null (Measure.addHaar_sphere _ _ _)
      (Measure.addHaar_sphere _ _ _))
  exact hgff.ae_lqgMeasure_eq_zero_of_isCompact_volume_eq_zero hγ hγ₂ hμ hK hvol

/-- The LQG mass of `annulus 0 3 6` is finite almost surely (zero-charge measure). -/
theorem ae_lqgMeasure_annulus_ne_top {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ ω ∂P, μ ω (annulus 0 3 6) ≠ ∞ := by
  have hK : IsCompact (closedBall (0 : ℂ) 6) := isCompact_closedBall _ _
  have hKR : closedBall (0 : ℂ) 6 ⊆ ball (0 : ℂ) 7 := closedBall_subset_ball (by norm_num)
  have hint := hgff.lintegral_lqgMeasure_le_volume_of_isCompact hμ hK hKR
  have hfin : ∫⁻ ω, μ ω (closedBall (0 : ℂ) 6) ∂P ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (zeroChargeLocalConst_ne_top γ 7) hK.measure_lt_top.ne)
      hint
  have hae : AEMeasurable (fun ω => μ ω (closedBall (0 : ℂ) 6)) P :=
    (Measure.measurable_coe measurableSet_closedBall).comp_aemeasurable
      (hgff.aemeasurable_lqgMeasure hμ)
  filter_upwards [ae_lt_top' hae hfin] with ω hω
  exact ne_top_of_le_ne_top hω.ne (measure_mono (inter_subset_left.trans ball_subset_closedBall))

/-- Outside first certificate of the fixed configuration: an event measurable for `fixedPinnedSigma hC`
and almost surely equal to the open first certificate. -/
theorem fixed_outside_first_certificate_rep {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    (hξ : 0 < ξ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ A : Set Ω, MeasurableSet[fixedPinnedSigma hC] A ∧
      A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) fixedW fixedT fixedQ' fixedQ fixedDelta} := by
  obtain ⟨A, hA, -, hArep⟩ :=
    isCorrectedPinchConfiguration_fixed.exists_positive_outside_first_certificate hξ hgff 𝔇 h𝔇
  exact ⟨A, comap_localModConstPairings_outside_le_fixedPinnedSigma hC _ hA, hArep⟩

/-- Outside version of the sphere separation `a₀` of the fixed configuration. -/
theorem fixed_outside_sphere_rep {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hgff : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ a : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ a ∧
      a =ᵐ[P] fun ω => ENNReal.ofReal
        (setDist (𝔇 (hC ω)) (sphere 0 fixedDelta) (sphere 0 (2 * fixedDelta))) := by
  obtain ⟨a, ha, hae⟩ :=
    isCorrectedPinchConfiguration_fixed.exists_outside_baseMetric_sphere_distance hgff 𝔇 h𝔇
  exact ⟨a, ha.mono (comap_localModConstPairings_outside_le_fixedPinnedSigma hC) le_rfl, hae⟩

/-- Outside version of the Green threshold `M · S` on the annulus `annulus 0 3 6` of the fixed configuration. -/
theorem fixed_outside_green_rep {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) (M : ℝ) :
    ∃ b : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ b ∧
      b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 := by
  have hα : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ) (half_pos hγ)
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ₂ hα Ω P hC hcirc μ hgff hμ
  have hopen : IsOpen (annulus (0 : ℂ) 3 6) := isOpen_ball.sdiff isClosed_closedBall
  have hne : (annulus (0 : ℂ) 3 6).Nonempty := by
    refine ⟨4, ?_, ?_⟩
    · rw [mem_ball_zero_iff]
      norm_num
    · rw [mem_closedBall_zero_iff]
      norm_num
  have hpos : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 3 6) := hfull.mono fun ω hω => hω _ hopen hne
  obtain ⟨b, hb, hbe⟩ :=
    isCorrectedPinchConfiguration_fixed.exists_outside_green_threshold hgff hμ
      (ae_lqgMeasure_frontier_annulus_zero_three_six_eq_zero hgff hγ hγ₂ hμ)
      (ae_lqgMeasure_annulus_ne_top hgff hμ) hpos M
  exact ⟨b, hb.mono (comap_localModConstPairings_outside_le_fixedPinnedSigma hC) le_rfl, hbe⟩

#print axioms fixed_outside_first_certificate_rep
#print axioms fixed_outside_sphere_rep
#print axioms fixed_outside_green_rep

end HarmonicBalls
