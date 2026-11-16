import HarmonicBalls.Proofs.Potential.LQGClockCellSecondMoment
import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIncrement

/-! # Brownian annular cell moments

The Brownian interval estimate transfers to the field-path product law and
the half-open time intervals used by clock cells.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A subcritical annular cell has a second-moment bound uniform in all
smoothing scales at most the inner radius. -/
theorem exists_lintegral_prod_brownian_annular_inserted_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ δ →
      ∀ (u h : ℝ), 0 ≤ u → 0 < h →
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc u (u + h), ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))) ^ 2
          ∂(P.prod (planarBrownianMotion x))) ≤
        C * (ENNReal.ofReal h) ^ (2 - γ ^ 2 / 2) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_brownian_annular_inserted_cell_sq_le hh x hγ hγ2 α δ
  refine ⟨C, hC, ?_⟩
  intro ε hε hεδ u h hu hhpos
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc u (u + h)))
  let A : Set ℂ := {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  let F : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun p =>
    ∫⁻ s in Ioc u (u + h), ENNReal.ofReal
      (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))
  have hF : AEMeasurable (fun p => (F p) ^ 2) (P.prod (planarBrownianMotion x)) :=
    (aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x) hε γ α δ u (u+h)).pow_const 2
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hmeas : ∀ᵐ ω ∂P, Measurable (fun z => ENNReal.ofReal
      (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    have hm : Measurable (fun z : ℂ => ENNReal.ofReal
        (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          (H ω ε w - H ω 1 0 - α * Real.log (max ε ‖w‖)))) z)) := by
      apply ENNReal.measurable_ofReal.comp
      exact (measurable_const.mul (measurable_const.mul
        ((((hHm ε hε).comp (measurable_id.prodMk measurable_const)).sub measurable_const).sub
          (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp).indicator hA
    convert hm using 1
    ext z
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε z hε]
    · rfl
  have heq (b : ContinuousPath ℂ) : ∀ᵐ ω ∂P,
      F (ω,b) = ∫⁻ t, ENNReal.ofReal (A.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b t)) ∂ν := by
    filter_upwards [hmeas] with ω hω
    dsimp [F, ν]
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    symm
    exact lintegral_map (hω.comp b.continuous.measurable) continuous_real_toNNReal.measurable
  have hswap : (∫⁻ p, (F p)^2 ∂(P.prod (planarBrownianMotion x))) =
      ∫⁻ b, ∫⁻ ω, (F (ω,b))^2 ∂P ∂(planarBrownianMotion x) :=
    lintegral_prod_symm _ hF
  change (∫⁻ p, (F p)^2 ∂(P.prod (planarBrownianMotion x))) ≤ _
  rw [hswap]
  refine (le_of_eq ?_).trans (hbound hε hεδ u h hu hhpos)
  apply lintegral_congr
  intro b
  apply lintegral_congr_ae
  filter_upwards [heq b] with ω hω
  rw [hω]

/-- The annular mesh-cell moment has a power strictly greater than one for
squared coupling below two, uniformly over scales at most the inner radius. -/
theorem exists_lintegral_prod_annular_mesh_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ) :
    ∃ (C : ℝ≥0∞) (β : ℝ), C < ∞ ∧ 0 < β ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ δ →
      ∀ (m : ℕ), 0 < m → ∀ j : Fin m,
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))) ^ (2 : ℝ)
          ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-(1 + 2 * β)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_annular_inserted_cell_sq_le hh x hγ hγ2 α δ
  refine ⟨C, (1 - γ ^ 2 / 2) / 2, hC, by linarith, ?_⟩
  intro ε hε hεδ m hm j
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hend : ((j : ℝ) / m) + 1 / (m : ℝ) = ((j : ℝ) + 1) / m := by ring
  have hrpow : (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 - γ ^ 2 / 2) =
      (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hm0, ENNReal.ofReal_natCast,
      ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    congr 1
    ring
  have hmain := hbound hε hεδ ((j : ℝ) / m) (1 / (m : ℝ))
    (div_nonneg hj0 hm0.le) (one_div_pos.mpr hm0)
  rw [hend, hrpow] at hmain
  simpa only [ENNReal.rpow_ofNat] using hmain

end HarmonicBalls
