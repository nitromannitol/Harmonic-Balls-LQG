import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement
import LatticeProb.Analysis.MonotoneGridApprox
import LatticeProb.LQG.LQGMassAlgebra

/-! # Expected uniform increments of monotone clocks

A grid estimate reduces a uniform clock increment to pointwise increments and a
mesh oscillation of one clock.
-/

namespace HarmonicBalls

open MeasureTheory Set MarkovProcess
open scoped ENNReal BigOperators

/-- The expected uniform difference of two monotone clocks is bounded by the sum of
expected grid-point differences and the expected mesh oscillation of one clock. -/
theorem lintegral_iSup_abs_sub_le_grid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ℝ → ℝ) {T : ℝ} (hT : 0 ≤ T) {m : ℕ} (hm : 0 < m)
    (hf : ∀ ω, MonotoneOn (f ω) (Icc 0 T))
    (hg : ∀ ω, MonotoneOn (g ω) (Icc 0 T))
    (hgrid : ∀ j : ℕ, Measurable (fun ω => |f ω (j * T / m) - g ω (j * T / m)|))
    (K : Ω → ℝ) (hK0 : ∀ ω, 0 ≤ K ω)
    (hK : ∀ ω j, j < m → g ω ((j + 1) * T / m) - g ω (j * T / m) ≤ K ω) :
    (∫⁻ ω, ⨆ t : Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t| ∂μ) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ ω, ENNReal.ofReal |f ω (j * T / m) - g ω (j * T / m)| ∂μ) +
        ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ := by
  let D : Ω → ℝ := fun ω => ∑ j ∈ Finset.range (m + 1),
    |f ω (j * T / m) - g ω (j * T / m)|
  have hDm : Measurable D := by
    exact Finset.measurable_sum _ (fun j _ => hgrid j)
  have hD0 (ω : Ω) : 0 ≤ D ω := by
    exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hpoint (ω : Ω) :
      (⨆ t : Icc (0 : ℝ) T, ENNReal.ofReal |f ω t - g ω t|) ≤
        ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω) := by
    apply iSup_le
    intro t
    rw [← ENNReal.ofReal_add (hD0 ω) (hK0 ω)]
    apply ENNReal.ofReal_le_ofReal
    apply LatticeProb.abs_sub_le_of_grid hm hT (hf ω) (hg ω) ?_ (hK ω) t t.property
    intro j hj
    change |f ω (j * T / m) - g ω (j * T / m)| ≤
      ∑ i ∈ Finset.range (m + 1), |f ω (i * T / m) - g ω (i * T / m)|
    exact Finset.single_le_sum (s := Finset.range (m + 1)) (a := j)
      (f := fun i : ℕ => |f ω (i * T / m) - g ω (i * T / m)|)
      (fun i _ => abs_nonneg (f ω (i * T / m) - g ω (i * T / m)))
      (show j ∈ Finset.range (m + 1) from Finset.mem_range.mpr (by omega))
  calc
    _ ≤ ∫⁻ ω, (ENNReal.ofReal (D ω) + ENNReal.ofReal (K ω)) ∂μ :=
      lintegral_mono hpoint
    _ = (∫⁻ ω, ENNReal.ofReal (D ω) ∂μ) + ∫⁻ ω, ENNReal.ofReal (K ω) ∂μ :=
      lintegral_add_left (ENNReal.measurable_ofReal.comp hDm) _
    _ = _ := by
      congr 1
      simp only [D, ENNReal.ofReal_sum_of_nonneg (fun _ _ => abs_nonneg _)]
      exact lintegral_finsetSum (Finset.range (m + 1))
        (f := fun j ω => ENNReal.ofReal |f ω (j * T / m) - g ω (j * T / m)|)
        (fun j _ => ENNReal.measurable_ofReal.comp (hgrid j))

/-- The expected maximum of finitely many nonnegative variables is controlled by
 their summed moments of any order at least one. -/
theorem lintegral_iSup_le_rpow_sum_lintegral_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (X : Fin m → Ω → ℝ≥0∞)
    (hX : ∀ j, Measurable (X j)) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, ⨆ j, X j ω ∂μ) ≤
      (∑ j, ∫⁻ ω, X j ω ^ p ∂μ) ^ (1 / p) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < 1 / p := one_div_pos.mpr hp0
  have hq1 : 1 / p ≤ 1 := (div_le_one hp0).2 hp
  let Y : Ω → ℝ≥0∞ := fun ω => (⨆ j, X j ω) ^ p
  have hYm : Measurable Y := (Measurable.iSup hX).pow_const p
  have hpoint (ω : Ω) : Y ω ≤ ∑ j, X j ω ^ p := by
    dsimp [Y]
    rw [(ENNReal.monotone_rpow_of_nonneg hp0.le).map_iSup_of_continuousAt
      (ENNReal.continuous_rpow_const (y := p)).continuousAt (by simp [hp0])]
    exact iSup_le fun j => Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin m => X i ω ^ p) (fun _ _ => zero_le) (Finset.mem_univ j)
  calc
    _ = ∫⁻ ω, Y ω ^ (1 / p) ∂μ := by
      congr 1
      funext ω
      dsimp [Y]
      rw [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one]
    _ ≤ (∫⁻ ω, Y ω ∂μ) ^ (1 / p) :=
      LatticeProb.lintegral_rpow_le_rpow_lintegral μ hq0 hq1 hYm.aemeasurable
    _ ≤ (∫⁻ ω, ∑ j, X j ω ^ p ∂μ) ^ (1 / p) :=
      ENNReal.rpow_le_rpow (lintegral_mono hpoint) hq0.le
    _ = _ := by
      congr 1
      exact lintegral_finsetSum _ (fun j _ => (hX j).pow_const p)


/-- A power bound on each cell moment controls the expected maximum by the
corresponding mesh power. -/
theorem lintegral_iSup_le_mesh_rpow {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (hm : 0 < m)
    (X : Fin m → Ω → ℝ≥0∞) (hX : ∀ j, Measurable (X j))
    {p β : ℝ} (hp : 1 ≤ p) (C : ℝ≥0∞)
    (hcell : ∀ j, (∫⁻ ω, X j ω ^ p ∂μ) ≤ C * (m : ℝ≥0∞) ^ (-(1 + p * β))) :
    (∫⁻ ω, ⨆ j, X j ω ∂μ) ≤ C ^ (1 / p) * (m : ℝ≥0∞) ^ (-β) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hm0 : (m : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hmt : (m : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top m
  have hsum : (∑ j, ∫⁻ ω, X j ω ^ p ∂μ) ≤
      (m : ℝ≥0∞) * (C * (m : ℝ≥0∞) ^ (-(1 + p * β))) := by
    calc
      _ ≤ ∑ _j : Fin m, C * (m : ℝ≥0∞) ^ (-(1 + p * β)) :=
        Finset.sum_le_sum (fun j _ => hcell j)
      _ = _ := by simp
  calc
    _ ≤ (∑ j, ∫⁻ ω, X j ω ^ p ∂μ) ^ (1 / p) :=
      lintegral_iSup_le_rpow_sum_lintegral_rpow μ X hX hp
    _ ≤ ((m : ℝ≥0∞) * (C * (m : ℝ≥0∞) ^ (-(1 + p * β)))) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hsum (one_div_nonneg.mpr hp0.le)
    _ = C ^ (1 / p) * (m : ℝ≥0∞) ^ (-β) := by
      have he : -(1 + p * β) = -1 + -(p * β) := by ring
      rw [he, ENNReal.rpow_add _ _ hm0 hmt, ENNReal.rpow_neg_one]
      rw [show (m : ℝ≥0∞) * (C * ((m : ℝ≥0∞)⁻¹ * (m : ℝ≥0∞) ^ (-(p * β)))) =
        C * ((m : ℝ≥0∞) * (m : ℝ≥0∞)⁻¹) * (m : ℝ≥0∞) ^ (-(p * β)) by ac_rfl]
      rw [ENNReal.mul_inv_cancel hm0 hmt, mul_one,
        ENNReal.mul_rpow_of_nonneg _ _ (one_div_nonneg.mpr hp0.le), ← ENNReal.rpow_mul]
      congr 1
      congr 1
      field_simp

/-- An annular clock cell is jointly measurable in the field and Brownian path. -/
theorem measurable_annular_clock_cell {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (γ α δ a b : ℝ)
    (hH : ∀ r : ℝ, 0 < r → Measurable (fun p : Ω × ℂ => H p.1 r p.2)) :
    Measurable (fun p : Ω × ContinuousPath ℂ =>
      ∫⁻ s in Ioc a b, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.1 ε z - H p.1 1 0 -
            α * Real.log (max ε ‖z‖)))) (p.2 s.toNNReal))) := by
  have hev : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable.comp
      (measurable_fst.snd.prodMk measurable_snd)
  have h1 : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => H p.1.1 1 0) :=
    (hH 1 zero_lt_one).comp (measurable_fst.fst.prodMk measurable_const)
  have he : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => H p.1.1 ε (p.1.2 p.2.toNNReal)) :=
    (hH ε hε).comp (measurable_fst.fst.prodMk hev)
  have hA : MeasurableSet {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hf : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ =>
      ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.1.1 ε z - H p.1.1 1 0 -
          α * Real.log (max ε ‖z‖)))) (p.1.2 p.2.toNNReal))) := by
    apply ENNReal.measurable_ofReal.comp
    have hm : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.1.1 ε (p.1.2 p.2.toNNReal) -
          H p.1.1 1 0 - α * Real.log (max ε ‖p.1.2 p.2.toNNReal‖)))) :=
      measurable_const.mul (measurable_const.mul ((he.sub h1).sub
        (measurable_const.mul ((measurable_const.max hev.norm).log)))).exp
    convert hm.indicator (hev hA) using 1
    ext p
    rfl
  exact hf.lintegral_prod_right'

/-- A jointly measurable annular cell version agrees with the inserted-field cell
on one field event, simultaneously for positive scales, paths, and intervals. -/
theorem exists_measurable_annular_inserted_clock_cell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ α δ : ℝ) :
    ∃ H : Ω → ℝ → ℂ → ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ a b : ℝ,
        Measurable (fun p : Ω × ContinuousPath ℂ =>
          ∫⁻ s in Ioc a b, ENNReal.ofReal
            ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.1 ε z - H p.1 1 0 -
                α * Real.log (max ε ‖z‖)))) (p.2 s.toNNReal)))) ∧
      (∀ᵐ ω ∂P, ∀ (ε : ℝ), 0 < ε → ∀ (b : ContinuousPath ℂ) (a c : ℝ),
        (∫⁻ s in Ioc a c, ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω ε z - H ω 1 0 -
              α * Real.log (max ε ‖z‖)))) (b s.toNNReal))) =
        ∫⁻ s in Ioc a c, ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal))) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  refine ⟨H, ?_, ?_⟩
  · intro ε hε a b
    apply HarmonicBalls.measurable_annular_clock_cell H hε γ α δ a b
    intro r hr
    exact (hHm r hr).comp (measurable_snd.prodMk measurable_fst)
  · filter_upwards [hHae, HarmonicBalls.ae_recentered_inserted_circle_average hh α] with ω hω hrec
    intro ε hε b a c
    apply lintegral_congr
    intro s
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε _ hε]
    · rfl

/-- The actual inserted annular clock cell is almost everywhere measurable
under the product of the field law and an s-finite path law. -/
theorem aemeasurable_annular_inserted_clock_cell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure (ContinuousPath ℂ)) [SFinite ν]
    {ε : ℝ} (hε : 0 < ε) (γ α δ a b : ℝ) :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      ∫⁻ s in Ioc a b, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)))
      (P.prod ν) := by
  obtain ⟨H, hHm, hHae⟩ := HarmonicBalls.exists_measurable_annular_inserted_clock_cell hh γ α δ
  apply (hHm ε hε a b).aemeasurable.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hHae] with p hp
  exact hp ε hε p.2 a b

end HarmonicBalls
