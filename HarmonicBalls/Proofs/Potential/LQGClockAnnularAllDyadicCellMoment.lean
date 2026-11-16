import HarmonicBalls.Proofs.Potential.LQGClockAnnularCoarseCellMoment

/-! # Annular dyadic cell moments

A common second-moment bound holds for all dyadic scales and starting points.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

private theorem exists_uniform_brownian_annular_inserted_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {ε : ℝ}, 0 < ε → ε ≤ δ →
      ∀ (u h : ℝ), 0 ≤ u → 0 < h →
        let ν := Measure.map Real.toNNReal (volume.restrict (Set.Icc u (u + h)))
        (∫⁻ b, ∫⁻ ω, (∫⁻ t, ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b t)) ∂ν) ^ 2 ∂P
          ∂(planarBrownianMotion x)) ≤ C * (ENNReal.ofReal h) ^ (2 - γ ^ 2 / 2) := by
  obtain ⟨D, hD, henergy⟩ :=
    exists_planarBrownianMotion_interval_pair_enorm_rpow_neg 0 (sq_pos_of_ne_zero hγ) hγ2
  let A : ℝ≥0∞ := ENNReal.ofReal
    (Real.exp (|γ * α| * |Real.log δ|) ^ 2 * 2 ^ (γ ^ 2))
  refine ⟨A * D, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hD, ?_⟩
  intro x ε hε hεδ u h hu hhpos
  let ν := Measure.map Real.toNNReal (volume.restrict (Set.Icc u (u + h)))
  have hbound (b : ContinuousPath ℂ) :
      (∫⁻ ω, (∫⁻ t, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b t)) ∂ν) ^ 2 ∂P) ≤
      A * ∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν) :=
    lintegral_annular_inserted_path_sq_le_riesz hh ν b b.continuous.measurable hε hεδ hγ α
  have hm : Measurable (fun b : ContinuousPath ℂ => ∫⁻ p : ℝ≥0 × ℝ≥0,
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν)) := by
    have hk : Measurable (fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
        (ENNReal.ofReal ‖q.1 q.2.1 - q.1 q.2.2‖) ^ (-(γ ^ 2))) := by fun_prop
    exact hk.lintegral_prod_right'
  calc
    _ ≤ ∫⁻ b, A * (∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν))
          ∂(planarBrownianMotion x) := lintegral_mono hbound
    _ = A * (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0,
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν)
          ∂(planarBrownianMotion x)) := lintegral_const_mul A hm
    _ = (A * D) * (ENNReal.ofReal h) ^ (2 - γ ^ 2 / 2) := by
      have heq := henergy u h hu hhpos
      dsimp only at heq
      rw [lintegral_planarBrownianMotion_interval_pair_enorm_rpow_neg 0 u h _ hu hhpos] at heq
      rw [lintegral_planarBrownianMotion_interval_pair_enorm_rpow_neg x u h _ hu hhpos, heq]
      ac_rfl


private theorem exists_uniform_prod_brownian_annular_inserted_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {ε : ℝ}, 0 < ε → ε ≤ δ →
      ∀ (u h : ℝ), 0 ≤ u → 0 < h →
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc u (u + h), ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))) ^ 2
          ∂(P.prod (planarBrownianMotion x))) ≤
        C * (ENNReal.ofReal h) ^ (2 - γ ^ 2 / 2) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_brownian_annular_inserted_cell_sq_le hh hγ hγ2 α δ
  refine ⟨C, hC, ?_⟩
  intro x ε hε hεδ u h hu hhpos
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
  refine (le_of_eq ?_).trans (hbound x hε hεδ u h hu hhpos)
  apply lintegral_congr
  intro b
  apply lintegral_congr_ae
  filter_upwards [heq b] with ω hω
  rw [hω]


private theorem exists_uniform_small_annular_mesh_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ) :
    ∃ (C : ℝ≥0∞), C < ∞ ∧ 0 < (1 - γ ^ 2 / 2) / 2 ∧ ∀ (x : ℂ) {ε : ℝ}, 0 < ε → ε ≤ δ →
      ∀ (m : ℕ), 0 < m → ∀ j : Fin m,
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))) ^ (2 : ℝ)
          ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_uniform_prod_brownian_annular_inserted_cell_sq_le hh hγ hγ2 α δ
  refine ⟨C, hC, by linarith, ?_⟩
  intro x ε hε hεδ m hm j
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hj0 : (0 : ℝ) ≤ j := by positivity
  have hend : ((j : ℝ) / m) + 1 / (m : ℝ) = ((j : ℝ) + 1) / m := by ring
  have hrpow : (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 - γ ^ 2 / 2) =
      (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hm0, ENNReal.ofReal_natCast,
      ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    congr 1
    ring
  have hmain := hbound x hε hεδ ((j : ℝ) / m) (1 / (m : ℝ))
    (div_nonneg hj0 hm0.le) (one_div_pos.mpr hm0)
  rw [hend, hrpow] at hmain
  simpa only [ENNReal.rpow_ofNat] using hmain


/-- For squared coupling below two, one finite constant controls the second
moment of every annular dyadic mesh cell, uniformly in the starting point. -/
theorem exists_lintegral_prod_annular_all_dyadic_mesh_cell_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ 0 < (1 - γ ^ 2 / 2) / 2 ∧
      ∀ (k : ℕ) (x : ℂ) (m : ℕ), 0 < m → ∀ j : Fin m,
      (∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
        ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          (dyadicScale k) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale k) z))
              (p.2 s.toNNReal))) ^ (2 : ℝ) ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-(1 + 2 * ((1 - γ ^ 2 / 2) / 2))) := by
  obtain ⟨C₁, hC₁, hβ, hsmall⟩ := exists_uniform_small_annular_mesh_cell_sq_le hh hγ hγ2 α δ
  obtain ⟨C₂, hC₂, _, hlarge⟩ :=
    exists_lintegral_prod_annular_excluded_dyadic_mesh_cell_sq_le hh hγ2 α hδ
  refine ⟨max C₁ C₂, max_lt hC₁ hC₂, hβ, ?_⟩
  intro k x m hm j
  by_cases hk : dyadicScale k ≤ min (1 / 2) δ
  · exact (hsmall x (dyadicScale_pos k) (hk.trans (min_le_right _ _)) m hm j).trans
      (mul_le_mul' (le_max_left _ _) le_rfl)
  · exact (hlarge k (lt_of_not_ge hk) x m hm j).trans
      (mul_le_mul' (le_max_right _ _) le_rfl)

end HarmonicBalls
