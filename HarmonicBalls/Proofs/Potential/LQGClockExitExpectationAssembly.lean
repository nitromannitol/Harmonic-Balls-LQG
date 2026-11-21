import HarmonicBalls.Proofs.Potential.LQGClockInnerStoppedIncrement
import HarmonicBalls.Proofs.Potential.LQGClockExitIncrementUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockOfLocallyUniformLimit

/-! # Expected exit times of the inserted clock from regional increment bounds

Split the plane into the inner disc `‖z‖ < δ`, the annulus `δ ≤ ‖z‖ ≤ 1/2` and the exterior
`1/2 < ‖z‖`. For the clocks stopped at the exit time from a smooth bounded domain and capped
at time one, the inner increments have a summable bound uniform over the start whenever
`0 < γ * α` and `γ ^ 2 / 2 < 2 - γ * α`. Given summable bounds of the same kind for the
annular and the exterior increments, uniform over starts in the domain, the exit-time clock
approximations are uniformly integrable for almost every field, and every LQG clock that is
almost surely a time-change clock has finite expected exit time equal to the limit of the
expected Green integrals of the approximating measures.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- An interval integral along a path up to a time at most one is the integral against the
occupation measure of the path up to that time. -/
theorem intervalIntegral_path_eq_integral_occupation (F : ℂ → ℝ) (hF : Measurable F)
    (b : ContinuousPath ℂ) {u : ℝ≥0} (hu : u ≤ 1) :
    (∫ s in (0 : ℝ)..(u : ℝ), F (b s.toNNReal)) =
      ∫ z, F z ∂(Measure.map (fun t => b t)
        ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic u))) := by
  rw [integral_map b.continuous.measurable.aemeasurable hF.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => F (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hF.comp b.continuous.measurable).aestronglyMeasurable]
  rw [intervalIntegral.integral_of_le u.coe_nonneg, ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc]
  constructor
  · rintro ⟨h0, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, le_trans hT (by exact_mod_cast hu)⟩
  · rintro ⟨hs, h0, _⟩
    exact ⟨h0, (Real.toNNReal_le_iff_le_coe).mp hs⟩


variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Integrals of the inserted density over a region against stopped occupation measures are
almost everywhere measurable under the product law. -/
theorem aemeasurable_region_stopped_occupation
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) (k : ℕ) {S : Set ℂ}
    (hS : MeasurableSet S) (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ)
    (ν' : Measure (ContinuousPath ℂ)) [SFinite ν'] :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ => ∫ z, S.indicator (fun z =>
      (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z)) z
      ∂(Measure.map (fun t => p.2 t) ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ p.2))))) (P.prod ν') := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let d : ℝ := dyadicScale k
  have hd : 0 < d := dyadicScale_pos k
  let FH : Ω × ℂ → ℝ := fun q => S.indicator (fun z => d ^ (γ ^ 2 / 2) * Real.exp (γ *
    (H q.1 d z - H q.1 1 0 - α * Real.log (max d ‖z‖)))) q.2
  have hFH : Measurable FH := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 d q.2) := (hHm d hd).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 one_pos).comp ((measurable_const : Measurable fun _ : Ω × ℂ => (0 : ℂ)).prodMk
        measurable_fst)
    have h3 : Measurable (fun q : Ω × ℂ => d ^ (γ ^ 2 / 2) * Real.exp (γ *
        (H q.1 d q.2 - H q.1 1 0 - α * Real.log (max d ‖q.2‖)))) :=
      measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul ((h1.sub h2).sub
        (measurable_const.mul (Real.measurable_log.comp
          (measurable_const.max (measurable_norm.comp measurable_snd)))))))
    have heq : FH = (Prod.snd ⁻¹' S).indicator (fun q : Ω × ℂ => d ^ (γ ^ 2 / 2) * Real.exp (γ *
        (H q.1 d q.2 - H q.1 1 0 - α * Real.log (max d ‖q.2‖)))) := by
      funext q
      by_cases hq : q.2 ∈ S
      · rw [Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' S from hq)]
        exact Set.indicator_of_mem hq _
      · rw [Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' S from hq)]
        exact Set.indicator_of_notMem hq _
    rw [heq]
    exact h3.indicator (measurable_snd hS)
  have hm := (measurable_stopped_path_integral FH hFH τ hτ).comp measurable_swap
  refine hm.aemeasurable.congr ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν')).ae
    (hHae.and (ae_recentered_inserted_circle_average hh α))] with p hp
  obtain ⟨hω, hrec⟩ := hp
  simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
  congr 1
  funext z
  simp only [FH]
  by_cases hz : z ∈ S
  · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hω, hω, hrec d z hd]
  · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]

end HarmonicBalls
