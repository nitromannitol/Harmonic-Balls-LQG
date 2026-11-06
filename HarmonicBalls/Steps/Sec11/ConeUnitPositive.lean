import HarmonicBalls.Steps.Sec11.ConeThresholds
import HarmonicBalls.Steps.Sec11.ConeBumpInclusion
import HarmonicBalls.Proofs.GFF.ConeMassLocalRepresentation
import HarmonicBalls.Proofs.Sec11.ConeBadEventTransfer

/-! # Positive probability for a unit-scale cone event -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The unit-scale cone event has positive probability, conditional on the
scaled-ball mass, volume-growth and whole-plane measure-existence inputs. -/
theorem cone_unit_event_positive
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hE0 : LQGMeasureExistence P γ 0 hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    0 < P {ω | coneMassEvent (μ ω) Q M 1 0} := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  obtain ⟨n, m, hn, hp⟩ := exists_cone_mass_green_thresholds hS hgrowth hγ hγ2 hα hG hE0 hμ Q hQ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨c, hc, hheight⟩ := exists_cone_bump_height hγ (inv_pos.mpr hnR)
    (show 0 ≤ M * (m : ℝ) by positivity)
  obtain ⟨f, hf, _, _, hinner, houter⟩ := exists_cone_smooth_bump 0 (r := 1) (by norm_num) hc
  let ν : Ω → Measure ℂ := fun ω => (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))
  have hν : IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f) ν := by
    have hw := Section6.lqgMeasureWeylScaling Ω P γ α₀ hC hcirc hG hγ hγ2 hα μ hμ
    filter_upwards [hw] with ω hω
    exact hω f hf.continuous
  have hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U := by
    filter_upwards [Section6.ae_fullSupport_all_singular_limits hS P γ hγ hγ2 hC hcirc hG hE0, hμ]
      with ω hh hω
    exact hh α₀ (μ ω) hω
  have hcone : annulus (0 : ℂ) 1 (2 * 1) ∩ coneAt Q 0 ⊆ ball 0 7 := by
    intro x hx
    have := hx.1.1
    change dist x 0 < 7
    change dist x 0 < 2 * 1 at this
    linarith
  have hgreen : annulus (0 : ℂ) (3 * 1) (6 * 1) ⊆ ball 0 7 := by
    intro x hx
    have := hx.1
    change dist x 0 < 7
    change dist x 0 < 6 * 1 at this
    linarith
  have hqm : MeasurableSet (annulus (0 : ℂ) 1 (2 * 1) ∩ coneAt Q 0) :=
    (measurableSet_ball.diff measurableSet_closedBall).inter
      ((Homeomorph.addRight 0).measurableEmbedding.measurableSet_image.mpr hQm)
  obtain ⟨ε, hε, hdec⟩ := hG.exists_enclosing_fixedShift_coneMassEvent_representation
    (show (0 : ℝ) < 7 by norm_num) (show (7 : ℝ) < 8 by norm_num) hf.continuous hf.contDiffOn
    μ ν hμ hν hfull Q M 1 0 hqm hcone hgreen
  obtain ⟨B, hB, hE, hEp⟩ := hdec 0
  apply cone_event_pos_of_smooth_shift hG (by linarith [hε.1]) hε.2 hf.contDiffOn 0 hB
    (fun ω => coneMassEvent (μ ω) Q M 1 0) (fun ω => coneMassEvent (ν ω) Q M 1 0) hE hEp
    {ω | (n : ℝ≥0∞)⁻¹ < μ ω (annulus 0 1 2 ∩ coneAt Q 0) ∧
      annulusGreenPotentialSup (μ ω) 0 3 6 < (m : ℝ≥0∞)} hp
  filter_upwards [] with ω hω
  apply coneMassEvent_of_bump (μ ω) Q M 1 γ c 0 f hQm hinner houter
    (C₁ := (n : ℝ≥0∞)⁻¹) (C₂ := (m : ℝ≥0∞))
    (by simpa using hω.1.le) (by simpa using hω.2.le)
  have hreal : ENNReal.ofReal (M * (m : ℝ)) ≤ ENNReal.ofReal (Real.exp (γ * c) * (n : ℝ)⁻¹) :=
    ENNReal.ofReal_le_ofReal hheight
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at hreal
  simpa [ENNReal.ofReal_mul hM.le, ENNReal.ofReal_inv_of_pos hnR] using hreal

end HarmonicBalls

#print axioms HarmonicBalls.cone_unit_event_positive
