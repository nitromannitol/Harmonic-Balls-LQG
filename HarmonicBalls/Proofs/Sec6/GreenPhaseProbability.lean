import HarmonicBalls.Proofs.Sec6.GreenAnnulusPhaseBounds
import HarmonicBalls.Proofs.Sec6.GreenSizeWindow
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable

/-! # Green-potential windows over compact dyadic phases -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Volume growth gives Green size windows whose constants work simultaneously
for every phase in `[1/2,1]` at the origin. -/
theorem exists_greenSize_window_on_dyadic_phases
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] {γ : ℝ}
    (hγ : 0 < γ) (hγ₂ : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₂m C₂p : ℝ, 0 < C₂m ∧ 0 < C₂p ∧ ∀ s ∈ Icc (1 / 2 : ℝ) 1,
      P {ω | annulusGreenPotentialSup (μ ω) 0 (s / 4) (2 * s) /
        (μ ω) (annulus 0 (s / 4) (2 * s)) ∉
          Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  let A : Set ℂ := annulus 0 (1 / 4) 1
  let B : Set ℂ := annulus 0 (1 / 8) 2
  let X : Ω → ℝ≥0∞ := fun ω => annulusGreenPotentialSup (μ ω) 0 (1 / 4) 1 / (μ ω) B
  let Y : Ω → ℝ≥0∞ := fun ω => annulusGreenPotentialSup (μ ω) 0 (1 / 8) 2 / (μ ω) A
  have hA : MeasurableSet A := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hB : MeasurableSet B := (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  have hμm := hgff.aemeasurable_lqgMeasure hμ
  have hX : AEMeasurable X P :=
    (((measurable_annulusGreenPotentialSup 0 (1 / 4) 1).div
      (Measure.measurable_coe hB)).comp_aemeasurable hμm)
  have hY : AEMeasurable Y P :=
    (((measurable_annulusGreenPotentialSup 0 (1 / 8) 2).div
      (Measure.measurable_coe hA)).comp_aemeasurable hμm)
  have hneA : A.Nonempty := by
    refine ⟨(1 / 2 : ℂ), ?_⟩
    change dist (1 / 2 : ℂ) 0 < 1 ∧ ¬ dist (1 / 2 : ℂ) 0 ≤ 1 / 4
    norm_num [dist_eq_norm, Complex.norm_def]
  have hsub : A ⊆ B := by
    intro x hx
    exact ⟨ball_subset_ball (by norm_num) hx.1,
      fun h => hx.2 (closedBall_subset_closedBall (by norm_num) h)⟩
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ₂ hQ hgff hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ₂ hQ
    Ω P hC hcirc μ hgff hμ
  have hpos : ∀ᵐ ω ∂P, (0 < X ω ∧ X ω ≠ ∞) ∧ (0 < Y ω ∧ Y ω ≠ ∞) := by
    filter_upwards [hV, hfull] with ω hω hf
    let : IsLocallyFiniteMeasure (μ ω) := hω.1
    have hmassA : 0 < (μ ω) A := hf A (isOpen_ball.sdiff isClosed_closedBall) hneA
    have hmassB : 0 < (μ ω) B := lt_of_lt_of_le hmassA (measure_mono hsub)
    have hmassBt : (μ ω) B ≠ ∞ := by
      apply ne_top_of_le_ne_top (measure_ball_lt_top (μ := μ ω) (x := (0 : ℂ)) (r := 2)).ne
      exact measure_mono (fun _ hx => hx.1)
    have hmassAt : (μ ω) A ≠ ∞ := ne_top_of_le_ne_top hmassBt (measure_mono hsub)
    have hsmall : 0 < annulusGreenPotentialSup (μ ω) 0 (1 / 4) 1 :=
      annulusGreenPotentialSup_pos_of_fullSupport (μ ω) 0 (1 / 4) 1 hf hneA
    have hbig : 0 < annulusGreenPotentialSup (μ ω) 0 (1 / 8) 2 :=
      lt_of_lt_of_le hsmall (annulusGreenPotentialSup_mono (μ ω) 0 (by norm_num) (by norm_num))
    have hbigt : annulusGreenPotentialSup (μ ω) 0 (1 / 8) 2 ≠ ∞ :=
      annulusGreenPotentialSup_ne_top_of_volumeGrowth (by norm_num) (hω.2 2 (by norm_num))
    have hsmallt : annulusGreenPotentialSup (μ ω) 0 (1 / 4) 1 ≠ ∞ :=
      ne_top_of_le_ne_top hbigt (annulusGreenPotentialSup_mono (μ ω) 0 (by norm_num) (by norm_num))
    exact ⟨⟨ENNReal.div_pos hsmall.ne' hmassBt, ENNReal.div_ne_top hsmallt hmassB.ne'⟩,
      ⟨ENNReal.div_pos hbig.ne' hmassAt, ENNReal.div_ne_top hbigt hmassA.ne'⟩⟩
  have hhalf : 0 < δ / 2 := ENNReal.half_pos hδ.ne'
  obtain ⟨lo, lo', hlo, hlo', hlow⟩ :=
    exists_ennreal_window_of_ae_pos_ne_top P hX (hpos.mono fun _ h => h.1) hhalf
  obtain ⟨hi', hi, hhi', hhi, hhigh⟩ :=
    exists_ennreal_window_of_ae_pos_ne_top P hY (hpos.mono fun _ h => h.2) hhalf
  refine ⟨lo, hi, hlo, hhi, ?_⟩
  intro s hs
  let E : Set Ω := {ω | X ω ∉ Icc (ENNReal.ofReal lo) (ENNReal.ofReal lo')}
  let F : Set Ω := {ω | Y ω ∉ Icc (ENNReal.ofReal hi') (ENNReal.ofReal hi)}
  calc
    P {ω | annulusGreenPotentialSup (μ ω) 0 (s / 4) (2 * s) /
        (μ ω) (annulus 0 (s / 4) (2 * s)) ∉
          Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi)} ≤ P (E ∪ F) := by
      apply measure_mono
      intro ω hbad
      by_contra h
      have hEF : X ω ∈ Icc (ENNReal.ofReal lo) (ENNReal.ofReal lo') ∧
          Y ω ∈ Icc (ENNReal.ofReal hi') (ENNReal.ofReal hi) := by
        simpa [E, F] using h
      have hE := hEF.1
      have hF := hEF.2
      obtain ⟨hl, hu⟩ := annulusGreenPotentialRatio_bounds_on_dyadic_phases (μ ω) hs
      exact hbad ⟨hE.1.trans hl, hu.trans hF.2⟩
    _ ≤ P E + P F := measure_union_le E F
    _ ≤ δ / 2 + δ / 2 := add_le_add hlow hhigh
    _ = δ := ENNReal.add_halves δ

end HarmonicBalls.Section6
