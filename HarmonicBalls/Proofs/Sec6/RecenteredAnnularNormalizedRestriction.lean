import HarmonicBalls.Proofs.Sec6.AnnularNormalizedRestriction
import HarmonicBalls.Proofs.Sec6.RecenteredGoodAnnulusLocality
import HarmonicBalls.Proofs.Sec8.OrdinaryFieldNormalizedRestriction

/-! # Recentered annular normalized restrictions

The imported annulus iteration uses Leonardo Bonanno's proof of the
Gwynne–Miller lemma in `LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
The affine GFF and LQG coordinate-change laws are explicit hypotheses.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- After translation to the origin, the normalized LQG restriction to an
annulus has a version measurable in the recentered field modulo constants. -/
theorem exists_modConst_recentered_annular_normalizedRestriction
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (fieldSigmaAlgebraModConst 0 (affinePairing hC hcirc 1 z) (annulus 0 r R)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction ((μ ω).map (fun x => x - z)) (annulus 0 r R) := by
  let η := affineMeasure γ hcirc μ 1 z
  have hs : IsWholePlaneGFF P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z) :=
    hAff hgff 1 one_ne_zero z
  have hη : IsLQGMeasureOfField P γ 0 (affineCircle hcirc 1 z) η :=
    isLQGMeasureOfField_affine hCC hgff hγ hγ2 hμ one_ne_zero z
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hd := identDistrib_affineMeasure hgff hμ hAff hCC hγ hγ2 (a := 1) one_ne_zero z
  have hfront0 := ae_lqg_annulus_frontier_eq_zero_of_affine hgff hμ hAff hCC hγ hγ2
    0 hr (lt_trans hr hrR)
  have hmeas : MeasurableSet {m : Measure ℂ | m (frontier (annulus 0 r R)) = 0} :=
    measurableSet_eq_fun (Measure.measurable_coe isClosed_frontier.measurableSet) measurable_const
  have hfront : ∀ᵐ ω ∂P, η ω (frontier (annulus 0 r R)) = 0 :=
    hd.ae_snd hmeas hfront0
  have hnonempty : (annulus (0 : ℂ) r R).Nonempty := by
    refine ⟨(((r + R) / 2 : ℝ) : ℂ), ?_⟩
    have hm : 0 ≤ (r + R) / 2 := by linarith
    have hd : dist ((((r + R) / 2 : ℝ) : ℂ)) 0 = (r + R) / 2 := by
      simp only [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]
    change dist ((((r + R) / 2 : ℝ) : ℂ)) 0 < R ∧
      ¬ dist ((((r + R) / 2 : ℝ) : ℂ)) 0 ≤ r
    rw [hd]
    constructor <;> linarith
  have hfinite : ∀ᵐ ω ∂P, η ω (annulus 0 r R) ≠ ∞ := by
    filter_upwards [hη] with ω hω
    let : IsLocallyFiniteMeasure (η ω) := hω.isLocallyFiniteMeasure
    exact ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset)
  have hpositive : ∀ᵐ ω ∂P, 0 < η ω (annulus 0 r R) := by
    filter_upwards [hfull γ 0 hγ hγ2 hQ Ω P _ _ η hs hη] with ω hω
    exact hω _ (isOpen_ball.sdiff isClosed_closedBall) hnonempty
  obtain ⟨ν, hν, hνeq⟩ :=
    IsWholePlaneGFF.exists_modConst_annular_normalizedRestriction hs hη 0 hr.le hrR
      hfront hfinite hpositive
  refine ⟨ν, hν, ?_⟩
  filter_upwards [hνeq] with ω hω
  rw [hω]
  dsimp only [η, affineMeasure]
  rw [normalizedRestriction_smul _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
    ENNReal.ofReal_ne_top]
  simp only [div_one]

end HarmonicBalls.Section6
