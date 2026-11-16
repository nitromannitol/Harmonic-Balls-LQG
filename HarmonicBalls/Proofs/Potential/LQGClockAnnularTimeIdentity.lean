import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement
import HarmonicBalls.Defs.LBM

/-! # Annular clock time integrals

The spatial occupation integral of an annular density equals its bounded-time
integral along the path.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

private theorem stopped_occupation_integral_eq_time (b : ContinuousPath ℂ) (T : ℝ≥0)
    (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))) =
    ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) T : ℝ), f (b s.toNNReal) := by
  rw [integral_map b.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => f (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hf.comp b.continuous.measurable).aestronglyMeasurable]
  simp only [NNReal.coe_one]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ min (1 : ℝ) (T : ℝ) from le_min zero_le_one T.coe_nonneg), ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨hs, h0, h1⟩
    exact ⟨h0, h1, (Real.toNNReal_le_iff_le_coe).mp hs⟩
  · rintro ⟨h0, h1, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, h1⟩

/-- Almost surely, every path has the annular inserted clock density identity
at every bounded horizon. -/
theorem ae_annular_inserted_occupation_eq_time_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (T : ℝ≥0),
      (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z
        ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))) =
      ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) T : ℝ),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b s.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
  intro b T
  let F : ℂ → ℝ := fun z => A.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(H ω (ε/2) z-H ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H ω ε z-H ω 1 0 - α*Real.log (max ε ‖z‖)))) z
  have h1 : Measurable (fun z => H ω (ε/2) z) :=
    (hHm (ε/2) (half_pos hε)).comp (measurable_id.prodMk measurable_const)
  have h2 : Measurable (fun z => H ω ε z) :=
    (hHm ε hε).comp (measurable_id.prodMk measurable_const)
  have hF : Measurable F := by
    apply Measurable.indicator _ hA
    exact (measurable_const.mul (measurable_const.mul ((h1.sub measurable_const).sub
      (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub measurable_const).sub
      (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp)
  have heq : F = A.indicator (fun z =>
      (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) := by
    funext z
    simp only [F, Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hω, hrec (ε/2) z (half_pos hε), hrec ε z hε]
    · rfl
  rw [← heq]
  exact stopped_occupation_integral_eq_time b T F hF


/-- The annular occupation increment is the integral of the actual inserted
clock density difference over the same bounded path-dependent horizon. -/
theorem stoppedAnnularIncrement_eq_time_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    stoppedAnnularIncrement P hcirc γ α δ ε τ b =
    ∫ ω, |∫ s in (0 : ℝ)..(min (1 : ℝ≥0) (τ b) : ℝ),
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
          (b s.toNNReal)| ∂P := by
  rw [stoppedAnnularIncrement_eq_inserted_field hh hε γ α δ τ b]
  apply integral_congr_ae
  filter_upwards [ae_annular_inserted_occupation_eq_time_integral hh hε γ α δ] with ω hω
  rw [hω b (τ b)]

end HarmonicBalls
