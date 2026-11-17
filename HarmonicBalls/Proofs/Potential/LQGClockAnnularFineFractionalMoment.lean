import HarmonicBalls.Proofs.Potential.LQGClockAnnularCoarseCellMoment
import LatticeProb.LQG.LQGMassMoment

/-! # Fine-scale moments of inserted circle averages

The moment of the inserted density at a point has an explicit dependence on
its smoothing scale and the insertion point.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal

namespace HarmonicBalls

/-- The one-point moment of the inserted density at a circle contained in the
unit disc. -/
theorem lintegral_inserted_clock_density_rpow_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {z : ℂ} (hz : ‖z‖ + ε ≤ 1) (γ α : ℝ)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ ω, (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) ^ p ∂P) =
      ENNReal.ofReal (Real.exp (-(p * γ * α) * Real.log (max ε ‖z‖))) *
        ENNReal.ofReal (ε ^ (-(γ ^ 2 * p * (p - 1) / 2))) := by
  have hmeas : Measurable (fun ω =>
      (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))) ^ p) :=
    (Measurable.ennreal_ofReal ((measurable_const.mul
      (Real.measurable_exp.comp ((hh.measurable_circle ε z hε).const_mul γ))))).pow_const p
  have heq : ∀ᵐ ω ∂P,
      (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) ^ p =
      ENNReal.ofReal (Real.exp (-(p * γ * α) * Real.log (max ε ‖z‖))) *
        (ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z))) ^ p := by
    filter_upwards [ae_recentered_inserted_circle_average hh α,
      hh.ae_circleAverage_one_zero] with ω hω hzero
    rw [← hω ε z hε, hzero]
    simp only [sub_zero]
    have hsplit : γ * (hcirc ω ε z - α * Real.log (max ε ‖z‖)) =
        γ * hcirc ω ε z + (-(γ * α) * Real.log (max ε ‖z‖)) := by ring
    rw [hsplit, Real.exp_add]
    have hfactor : ε ^ (γ ^ 2 / 2) *
        (Real.exp (γ * hcirc ω ε z) * Real.exp (-(γ * α) * Real.log (max ε ‖z‖))) =
        Real.exp (-(γ * α) * Real.log (max ε ‖z‖)) *
          (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z)) := by ring
    rw [hfactor, ENNReal.ofReal_mul (by positivity), ENNReal.mul_rpow_of_nonneg _ _ hp,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp, ← Real.exp_mul]
    congr 3
    ring
  rw [lintegral_congr_ae heq, lintegral_const_mul _ hmeas,
    hh.lintegral_rpow_mul_exp_circle hε hz (γ ^ 2 / 2) γ hp]
  congr 2
  ring

/-- The moment of the annular density is bounded uniformly in the spatial
point, with explicit dependence on the smoothing scale and inner radius. -/
theorem lintegral_annular_inserted_clock_density_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) (γ α : ℝ) {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (∫⁻ ω, (ENNReal.ofReal
      ({w : ℂ | δ ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2}.indicator (fun w =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) z)) ^ p ∂P) ≤
      ENNReal.ofReal (Real.exp (|p * γ * α| * |Real.log δ|)) *
        ENNReal.ofReal (ε ^ (-(γ ^ 2 * p * (p - 1) / 2))) := by
  by_cases hz : δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hz]
    have hδ : 0 < δ := hε.trans_le hεδ
    have hz0 : 0 < ‖z‖ := hδ.trans_le hz.1
    have hlog : Real.log δ ≤ Real.log ‖z‖ := Real.log_le_log hδ hz.1
    have hlogz : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hz0.le (by linarith [hz.2])
    have hlogδ : Real.log δ ≤ 0 := hlog.trans hlogz
    have hw : -(p * γ * α) * Real.log (max ε ‖z‖) ≤
        |p * γ * α| * |Real.log δ| := by
      rw [max_eq_right (hεδ.trans hz.1)]
      calc
        _ ≤ |-(p * γ * α) * Real.log ‖z‖| := le_abs_self _
        _ = |p * γ * α| * |Real.log ‖z‖| := by rw [abs_mul, abs_neg]
        _ ≤ |p * γ * α| * |Real.log δ| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonpos hlogz, abs_of_nonpos hlogδ]
          linarith
    rw [lintegral_inserted_clock_density_rpow_eq hh hε (z := z)
      (by linarith [hz.1, hz.2]) γ α hp.le]
    gcongr
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hz,
      ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp, lintegral_zero, zero_le]

/-- At a positive smoothing scale, annular mass against a finite measure has
an explicit moment bound in terms of the mass of the measure. -/
theorem lintegral_annular_inserted_mass_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure ℂ) [SFinite ν] {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    (γ α : ℝ) {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, (∫⁻ z, ENNReal.ofReal
      ({u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator (fun u =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) ∂ν) ^ p ∂P) ≤
      (ENNReal.ofReal (Real.exp (|p * γ * α| * |Real.log δ|)) *
        ENNReal.ofReal (ε ^ (-(γ ^ 2 * p * (p - 1) / 2)))) * (ν Set.univ) ^ p := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}
  let f : ℂ → Ω → ℝ≥0∞ := fun z ω =>
    ENNReal.ofReal (A.indicator (fun u =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω ε u - H ω 1 0 -
        α * Real.log (max ε ‖u‖)))) z)
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hf : Measurable (Function.uncurry f) := by
    apply ENNReal.measurable_ofReal.comp
    have he : Measurable (fun p : ℂ × Ω => H p.2 ε p.1) := hHm ε hε
    have h1 : Measurable (fun p : ℂ × Ω => H p.2 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_snd)
    have hm : Measurable (fun p : ℂ × Ω =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.2 ε p.1 - H p.2 1 0 -
          α * Real.log (max ε ‖p.1‖)))) :=
      measurable_const.mul (measurable_const.mul ((he.sub h1).sub
        (measurable_const.mul ((measurable_const.max measurable_fst.norm).log)))).exp
    convert hm.indicator (measurable_fst hA) using 1
    ext p
    rfl
  have hae : ∀ᵐ ω ∂P, ∀ z, f z ω = ENNReal.ofReal (A.indicator (fun u =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    intro z
    dsimp [f]
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε z hε]
    · rfl

  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|p * γ * α| * |Real.log δ|)) *
    ENNReal.ofReal (ε ^ (-(γ ^ 2 * p * (p - 1) / 2)))
  have hK (z : ℂ) : (∫⁻ ω, f z ω ^ p ∂P) ≤ C := by
    have heq : (∫⁻ ω, f z ω ^ p ∂P) =
        ∫⁻ ω, (ENNReal.ofReal (A.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z)) ^ p ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω z]
    rw [heq]
    exact lintegral_annular_inserted_clock_density_rpow_le hh hε hεδ γ α (by linarith) z
  have hmain : (∫⁻ ω, (∫⁻ z, f z ω ∂ν) ^ p ∂P) ≤ C * (ν Set.univ) ^ p := by
    calc
      _ ≤ ∫⁻ ω, (ν Set.univ) ^ (p - 1) * ∫⁻ z, f z ω ^ p ∂ν ∂P := by
        apply lintegral_mono
        intro ω
        exact LatticeProb.lintegral_rpow_le_measure_univ_mul ν hp
          ((hf.comp (measurable_id.prodMk measurable_const)).aemeasurable)
      _ = (ν Set.univ) ^ (p - 1) * ∫⁻ z, ∫⁻ ω, f z ω ^ p ∂P ∂ν := by
        rw [lintegral_const_mul]
        · rw [lintegral_lintegral_swap]
          exact ((hf.pow_const p).comp measurable_swap).aemeasurable
        · exact (hf.pow_const p).lintegral_prod_left'
      _ ≤ (ν Set.univ) ^ (p - 1) * ∫⁻ _ : ℂ, C ∂ν := by
        gcongr with z
        exact hK z
      _ = C * (ν Set.univ) ^ p := by
        rw [lintegral_const]
        calc
          _ = C * ((ν Set.univ) ^ (p - 1) * ν Set.univ) := by ac_rfl
          _ = C * (ν Set.univ) ^ ((p - 1) + 1) := by
            rw [ENNReal.rpow_add_of_nonneg (p - 1) 1 (by linarith) (by norm_num),
              ENNReal.rpow_one]
          _ = _ := by congr 2; ring
  have heq : (∫⁻ ω, (∫⁻ z, f z ω ∂ν) ^ p ∂P) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (A.indicator (fun u =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) ∂ν) ^ p ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hae] with ω hω
    congr 1
    exact lintegral_congr fun z => hω z
  rw [heq] at hmain
  exact hmain

/-- At a positive smoothing scale, the moment of an annular Brownian time
cell is bounded uniformly in the starting point and cell location. -/
theorem lintegral_prod_brownian_annular_cell_rpow_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (γ α u h : ℝ)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ t in Ioc u (u + h), ENNReal.ofReal
      ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 t.toNNReal))) ^ p
          ∂(P.prod (planarBrownianMotion x))) ≤
      (ENNReal.ofReal (Real.exp (|p * γ * α| * |Real.log δ|)) *
        ENNReal.ofReal (ε ^ (-(γ ^ 2 * p * (p - 1) / 2)))) * (ENNReal.ofReal h) ^ p := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let A : Set ℂ := {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|p * γ * α| * |Real.log δ|)) *
    ENNReal.ofReal (ε ^ (-(γ ^ 2 * p * (p - 1) / 2)))
  let F : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun q =>
    ∫⁻ s in Ioc u (u + h), ENNReal.ofReal
      (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))
  have hF : AEMeasurable (fun q => (F q) ^ p) (P.prod (planarBrownianMotion x)) :=
    (aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x) hε γ α δ u (u+h)).pow_const p
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
  have hbound (b : ContinuousPath ℂ) : (∫⁻ ω, (F (ω,b)) ^ p ∂P) ≤
      C * (ENNReal.ofReal h) ^ p := by
    let g : ℝ → ℂ := fun s => b s.toNNReal
    have hg : Measurable g := b.continuous.measurable.comp continuous_real_toNNReal.measurable
    let ν : Measure ℂ := Measure.map g (volume.restrict (Ioc u (u+h)))
    have hν : ν Set.univ = ENNReal.ofReal h := by
      rw [show ν = Measure.map g (volume.restrict (Ioc u (u+h))) from rfl,
        Measure.map_apply hg MeasurableSet.univ]
      simp only [preimage_univ, Measure.restrict_apply_univ, Real.volume_Ioc]
      congr 1
      ring
    have heq : (∫⁻ ω, (F (ω,b)) ^ p ∂P) =
        ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (A.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z) ∂ν) ^ p ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hmeas] with ω hω
      dsimp [F, ν]
      rw [lintegral_map hω hg]
    rw [heq, ← hν]
    exact lintegral_annular_inserted_mass_rpow_le hh ν hε hεδ γ α hp
  change (∫⁻ q, (F q) ^ p ∂(P.prod (planarBrownianMotion x))) ≤ _
  rw [lintegral_prod_symm _ hF]
  calc
    _ ≤ ∫⁻ _ : ContinuousPath ℂ, C * (ENNReal.ofReal h) ^ p ∂(planarBrownianMotion x) :=
      lintegral_mono hbound
    _ = _ := by
      simp only [lintegral_const, measure_univ, mul_one]
      rfl

end HarmonicBalls
