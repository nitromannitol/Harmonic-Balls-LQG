import HarmonicBalls.Proofs.Potential.LQGClockAnnularCoarseCellMoment
import LatticeProb.LQG.LQGMassMoment
import LatticeProb.LQG.LQGSubSquareGaussian
import LatticeProb.Prob.GaussKahaneRpow
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-! # Fine-scale moments of inserted circle averages

The moment of the inserted density at a point has an explicit dependence on
its smoothing scale and the insertion point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal Topology
open Filter

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

/-- On an annulus the insertion changes the clock density by at most a
constant independent of the smoothing scale. -/
theorem ae_annular_inserted_clock_density_le_uninserted
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      ENNReal.ofReal ({w : ℂ | δ ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2}.indicator (fun w =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) z) ≤
      ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|)) *
        ENNReal.ofReal ({w : ℂ | δ ≤ ‖w‖ ∧ ‖w‖ ≤ 1 / 2}.indicator (fun w =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε w)) z) := by
  filter_upwards [ae_recentered_inserted_circle_average hh α,
    ae_recentered_inserted_circle_average hh 0] with ω hα h0
  intro z
  by_cases hz : δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left hz]
    rw [← hα ε z hε, ← h0 ε z hε]
    simp only [zero_mul, sub_zero]
    have hδ : 0 < δ := hε.trans_le hεδ
    have hz0 : 0 < ‖z‖ := hδ.trans_le hz.1
    have hlog : Real.log δ ≤ Real.log ‖z‖ := Real.log_le_log hδ hz.1
    have hlogz : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hz0.le (by linarith [hz.2])
    have hlogδ : Real.log δ ≤ 0 := hlog.trans hlogz
    have hw : -(γ * α) * Real.log (max ε ‖z‖) ≤
        |γ * α| * |Real.log δ| := by
      rw [max_eq_right (hεδ.trans hz.1)]
      calc
        _ ≤ |-(γ * α) * Real.log ‖z‖| := le_abs_self _
        _ = |γ * α| * |Real.log ‖z‖| := by rw [abs_mul, abs_neg]
        _ ≤ |γ * α| * |Real.log δ| := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [abs_of_nonpos hlogz, abs_of_nonpos hlogδ]
          linarith
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have he : Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0 -
        α * Real.log (max ε ‖z‖))) ≤
        Real.exp (|γ * α| * |Real.log δ|) *
          Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    have hs : 0 ≤ ε ^ (γ ^ 2 / 2) := Real.rpow_nonneg hε.le _
    nlinarith
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_right hz,
      ENNReal.ofReal_zero, mul_zero, le_refl]

/-- The annular occupation mass of the inserted field is bounded by a
scale-independent multiple of that of the uninserted field. -/
theorem ae_annular_inserted_clock_cell_le_uninserted
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (γ α : ℝ)
    (ν : Measure ℝ) :
    ∀ᵐ ω ∂P, ∀ b : ℝ → ℂ,
      (∫⁻ t, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b t)) ∂ν) ≤
      ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|)) *
        (∫⁻ t, ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b t)) ∂ν) := by
  filter_upwards [ae_annular_inserted_clock_density_le_uninserted hh hε hεδ γ α] with ω hω
  intro b
  calc
    _ ≤ ∫⁻ t, ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|)) *
        ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc ω) ε z)) (b t)) ∂ν :=
      lintegral_mono fun t => hω (b t)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top


/-- The fractional moment of an inserted annular time cell is controlled by
that of the corresponding uninserted cell, uniformly in the smoothing scale. -/
theorem lintegral_prod_brownian_annular_inserted_cell_rpow_le_uninserted
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) (γ α u h : ℝ)
    {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ t in Ioc u (u + h), ENNReal.ofReal
      ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 t.toNNReal))) ^ p
          ∂(P.prod (planarBrownianMotion x))) ≤
      (ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|))) ^ p *
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ t in Ioc u (u + h), ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z)) (q.2 t.toNNReal))) ^ p
            ∂(P.prod (planarBrownianMotion x))) := by
  have hae := ae_annular_inserted_clock_cell_le_uninserted hh hε hεδ γ α
    (volume.restrict (Ioc u (u + h)))
  have hprod := (Measure.quasiMeasurePreserving_fst (μ := P)
    (ν := planarBrownianMotion x)).ae hae
  calc
    _ ≤ ∫⁻ q : Ω × ContinuousPath ℂ,
        (ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|))) ^ p *
        (∫⁻ t in Ioc u (u + h), ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage 0 (hcirc q.1) ε z))
                (q.2 t.toNNReal))) ^ p ∂(P.prod (planarBrownianMotion x)) := by
          apply lintegral_mono_ae
          filter_upwards [hprod] with q hq
          exact (ENNReal.rpow_le_rpow (hq (fun t => q.2 t.toNNReal)) hp).trans_eq
            (ENNReal.mul_rpow_of_nonneg _ _ hp)
    _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)

/-- The circle-average covariance is bounded by the logarithmic kernel with
cutoff at the smoothing scale, including coincident points. -/
theorem covariance_circle_le_log_max
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ}
    (hε : 0 < ε) {z w : ℂ} (hz : ‖z‖ + ε ≤ 1) (hw : ‖w‖ + ε ≤ 1) :
    ProbabilityTheory.covariance (fun ω => hcirc ω ε z) (fun ω => hcirc ω ε w) P ≤
      Real.log 2 - Real.log (max ε ‖z - w‖) := by
  by_cases hdist : ‖z - w‖ ≤ ε
  · have hp : Real.log ε ≤ LatticeProb.Gauss.circlePairPotential z ε w ε := by
      have h := Real.circleAverage_mono (c := z) (R := ε)
        (f₁ := fun _ : ℂ => Real.log ε)
        (f₂ := fun a => Real.log (max ε ‖a - w‖))
        (continuous_const.continuousOn.circleIntegrable')
        (LatticeProb.Gauss.continuous_log_max_norm_sub hε w).continuousOn.circleIntegrable' ?_
      · simpa [LatticeProb.Gauss.circlePairPotential, Real.circleAverage_const] using h
      · intro a _ha
        exact Real.log_le_log hε (le_max_left _ _)
    rw [hh.covariance_circle_inside hε hε hz hw, max_eq_left hdist]
    have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · have hne : z ≠ w := by
      intro heq
      subst w
      simp only [sub_self, norm_zero] at hdist
      exact hdist hε.le
    have h := hh.covariance_circle_le_log_two hε hz hw hne
    rw [max_eq_right (le_of_not_ge hdist)]
    exact h



/-- Positive moments of finite weighted circle-average samples on two pieces
are bounded by those of the independent-piece comparison field. -/
theorem integral_rpow_subSquareField_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (piece : ι → Fin 2) (pt : ι → ℂ)
    (hpt : ∀ i, pt i ∈ LatticeProb.LQG.lqgSquare)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {q : ℝ} (hq : 1 ≤ q) :
    ∫ ω, (∑ i, p i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) piece pt ω i -
      ProbabilityTheory.variance (fun ω => LatticeProb.Gauss.subSquareField γ hcirc
        (LatticeProb.LQG.dyadicScale k) (LatticeProb.LQG.dyadicScale k * δ)
        piece pt ω i) P / 2)) ^ q ∂P ≤
    ∫ x, (∑ i, p i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc (LatticeProb.LQG.dyadicScale k)
        δ piece pt x i -
      ProbabilityTheory.variance (fun x => LatticeProb.Gauss.subSquareComparison γ hcirc
        (LatticeProb.LQG.dyadicScale k) δ piece pt x i)
        (LatticeProb.Gauss.subSquareMeasure P) / 2)) ^ q
      ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  have hR := LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k
  exact LatticeProb.Kahane.kahane_convexity_rpow (Or.inr hq) hp
    (hh.hasGaussianLaw_subSquareField γ (mul_pos hR hδ) piece pt)
    (hh.hasGaussianLaw_subSquareComparison γ hR hδ piece pt)
    (fun i => hh.integral_subSquareField γ (mul_pos hR hδ) piece pt i)
    (fun i => hh.integral_subSquareComparison γ hR hδ piece pt i)
    (fun i j => hh.covariance_subSquareField_le γ hk hδ hδ2 piece pt hpt i j)


/-- The two-piece comparison with the normalization constants written in
terms of the coarse and fine smoothing scales. -/
theorem integral_rpow_subSquareField_le_explicit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (piece : ι → Fin 2) (pt : ι → ℂ)
    (hpt : ∀ i, pt i ∈ LatticeProb.LQG.lqgSquare)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) {q : ℝ} (hq : 1 ≤ q) :
    ∫ ω, (∑ i, p i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) piece pt ω i -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)) ^ q ∂P ≤
    ∫ x, (∑ i, p i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc (LatticeProb.LQG.dyadicScale k)
        δ piece pt x i - γ ^ 2 *
        (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2)) ^ q
      ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  have hR := LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k
  have hz : ∀ s : Fin 2, ‖LatticeProb.LQG.lqgSquareCentre s‖ +
      LatticeProb.LQG.dyadicScale k ≤ 1 := fun s =>
    LatticeProb.LQG.norm_lqgSquareCentre_add_dyadicScale_le_one hk s
  have hn : ∀ i, ‖pt i‖ + δ ≤ 1 := fun i => by
    have hi : ‖pt i‖ ≤ 1 / 4 := by
      simpa using LatticeProb.LQG.lqgSquare_subset_closedBall (hpt i)
    linarith
  have hx : ∀ i, ‖(LatticeProb.LQG.dyadicScale k : ℂ) * pt i +
      LatticeProb.LQG.lqgSquareCentre (piece i)‖ +
        LatticeProb.LQG.dyadicScale k * δ ≤ 1 := fun i =>
    LatticeProb.Gauss.norm_rescaled_add_le hR (hz _) (hn i)
  have hvarX (i : ι) := hh.variance_subSquareField γ (mul_pos hR hδ) piece pt i (hx i)
  have hvarY (i : ι) := hh.variance_subSquareComparison γ hR hδ piece pt i (hz _) (hn i)
  simpa only [hvarX, hvarY] using
    integral_rpow_subSquareField_le hh γ hk hδ hδ2 piece pt hpt hp hq


/-- The finite two-piece moment comparison also permits vanishing weights. -/
theorem integral_rpow_subSquareField_le_explicit_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (piece : ι → Fin 2) (pt : ι → ℂ)
    (hpt : ∀ i, pt i ∈ LatticeProb.LQG.lqgSquare)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) {q : ℝ} (hq : 1 ≤ q) :
    ∫ ω, (∑ i, p i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) piece pt ω i -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)) ^ q ∂P ≤
    ∫ x, (∑ i, p i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc (LatticeProb.LQG.dyadicScale k)
        δ piece pt x i - γ ^ 2 *
        (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2)) ^ q
      ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  classical
  by_cases hpos : ∃ i, 0 < p i
  · let : Nonempty {i : ι // 0 < p i} := ⟨⟨hpos.choose, hpos.choose_spec⟩⟩
    have hsum (f : ι → ℝ) : (∑ i : {i : ι // 0 < p i}, p i * f i) =
        ∑ i, p i * f i := by
      rw [← Finset.sum_subtype (p := fun i => 0 < p i)
        (Finset.univ.filter (fun i => 0 < p i)) (by simp) (fun i => p i * f i)]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro i _ hi
      have hzero : p i = 0 := le_antisymm (le_of_not_gt (by simpa using hi)) (hp i)
      simp [hzero]
    have h := integral_rpow_subSquareField_le_explicit hh γ hk hδ hδ2
      (fun i : {i : ι // 0 < p i} => piece i)
      (fun i : {i : ι // 0 < p i} => pt i)
      (fun i => hpt i) (fun i => i.property) hq
    simp only [LatticeProb.Gauss.subSquareField,
      LatticeProb.Gauss.subSquareComparison] at h ⊢
    have hx (ω : Ω) := hsum (fun i => Real.exp
      (γ * hcirc ω (LatticeProb.LQG.dyadicScale k * δ)
        (↑(LatticeProb.LQG.dyadicScale k) * pt i +
          LatticeProb.LQG.lqgSquareCentre (piece i)) -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2))
    have hy (x : (Ω × ℝ) × (Fin 2 → Ω)) := hsum (fun i => Real.exp
      (γ * (hcirc x.1.1 (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.lqgSquareCentre (piece i)) + hcirc (x.2 (piece i)) δ (pt i) +
        x.1.2) - γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2))
    simp_rw [hx, hy] at h
    exact h
  · have hz : ∀ i, p i = 0 := fun i => le_antisymm (le_of_not_gt (fun hi => hpos ⟨i, hi⟩)) (hp i)
    simp [hz, Real.zero_rpow (by linarith : q ≠ 0)]

/-- The normalized comparison field has an explicit one-point moment. -/
theorem integral_exp_subSquareComparison_normalized_mul
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (piece : ι → Fin 2) (pt : ι → ℂ) (i : ι)
    (hc : ‖LatticeProb.LQG.lqgSquareCentre (piece i)‖ + R ≤ 1)
    (hp : ‖pt i‖ + δ ≤ 1) (r : ℝ) :
    (∫ x, Real.exp (r * (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i -
      γ ^ 2 * (1 - Real.log R - Real.log δ) / 2))
        ∂(LatticeProb.Gauss.subSquareMeasure P)) =
    Real.exp ((r ^ 2 - r) * (γ ^ 2 * (1 - Real.log R - Real.log δ)) / 2) := by
  let μ := LatticeProb.Gauss.subSquareMeasure P
  let X := fun x => LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i
  let V := γ ^ 2 * (1 - Real.log R - Real.log δ)
  have hG : HasGaussianLaw X μ :=
    (hh.hasGaussianLaw_subSquareComparison γ hR hδ piece pt).eval i
  have hm : ∫ x, X x ∂μ = 0 := hh.integral_subSquareComparison γ hR hδ piece pt i
  have hv : variance X μ = V := hh.variance_subSquareComparison γ hR hδ piece pt i hc hp
  have hv0 : 0 ≤ V := hv ▸ variance_nonneg X μ
  have hlaw : HasLaw X (gaussianReal 0 V.toNNReal) μ :=
    ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hm, hv]⟩
  have hmgf := mgf_gaussianReal hlaw r
  simp only [mgf, zero_mul, zero_add, Real.coe_toNNReal V hv0] at hmgf
  change (∫ x, Real.exp (r * (X x - V / 2)) ∂μ) = Real.exp ((r ^ 2 - r) * V / 2)
  simp_rw [show ∀ x, Real.exp (r * (X x - V / 2)) =
      Real.exp (-(r * V / 2)) * Real.exp (r * X x) by
    intro x
    rw [← Real.exp_add]
    congr 1
    ring]
  rw [integral_const_mul, hmgf, ← Real.exp_add]
  congr 1
  ring

/-- A normalized finite atomic comparison mass has an explicit moment bound. -/
theorem integral_rpow_sum_subSquareComparison_le_of_sum_eq_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (piece : ι → Fin 2) (pt : ι → ℂ)
    (hc : ∀ i, ‖LatticeProb.LQG.lqgSquareCentre (piece i)‖ + R ≤ 1)
    (hpt : ∀ i, ‖pt i‖ + δ ≤ 1) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (ha1 : ∑ i, a i = 1) {r : ℝ} (hr : 1 ≤ r) :
    (∫ x, (∑ i, a i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i -
        γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)) ^ r
      ∂(LatticeProb.Gauss.subSquareMeasure P)) ≤
    Real.exp ((r ^ 2 - r) * (γ ^ 2 * (1 - Real.log R - Real.log δ)) / 2) := by
  classical
  let μ := LatticeProb.Gauss.subSquareMeasure P
  let X := fun x i => LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i
  let V := γ ^ 2 * (1 - Real.log R - Real.log δ)
  let F := fun x i => Real.exp (X x i - V / 2)
  have hI (i : ι) : Integrable (fun x => F x i ^ r) μ := by
    let G := fun x => X x i
    have hG : HasGaussianLaw G μ :=
      (hh.hasGaussianLaw_subSquareComparison γ hR hδ piece pt).eval i
    have hL : HasLaw G (gaussianReal (∫ x, G x ∂μ) (variance G μ).toNNReal) μ :=
      ⟨hG.aemeasurable, hG.map_eq_gaussianReal⟩
    have hi := hL.integrable_comp (f := fun y : ℝ => Real.exp (r * y))
      (integrable_exp_mul_gaussianReal r)
    have heq : (fun x => F x i ^ r) =
        (fun x => Real.exp (-(r * V / 2)) * Real.exp (r * G x)) := by
      funext x
      dsimp [F, G]
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hi.const_mul _
  have hsum : Integrable (fun x => ∑ i, a i * F x i ^ r) μ := by
    exact integrable_finsetSum _ (fun i _ => (hI i).const_mul (a i))
  have hle (x) : (∑ i, a i * F x i) ^ r ≤ ∑ i, a i * F x i ^ r :=
    Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ a (F x)
      (fun i _ => ha i) ha1 (fun i _ => (Real.exp_pos _).le) hr
  have hmeas : AEStronglyMeasurable (fun x => (∑ i, a i * F x i) ^ r) μ := by
    have hf (i : ι) : AEStronglyMeasurable (fun x => F x i) μ := by
      have hg := ((hh.hasGaussianLaw_subSquareComparison γ hR hδ piece pt).eval i).aemeasurable
      exact ((hg.sub aemeasurable_const).exp).aestronglyMeasurable
    have hs : AEStronglyMeasurable (fun x => ∑ i, a i * F x i) μ := by
      convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => (hf i).const_mul (a i)) using 1
      ext x
      simp only [Finset.sum_apply]
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ r)).comp_aestronglyMeasurable hs
  have hint : Integrable (fun x => (∑ i, a i * F x i) ^ r) μ := by
    apply hsum.mono' hmeas
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (ha i) (Real.exp_pos _).le)) _)]
    exact hle x
  calc
    _ ≤ ∫ x, ∑ i, a i * F x i ^ r ∂μ := integral_mono hint hsum hle
    _ = ∑ i, a i * ∫ x, F x i ^ r ∂μ := by
      rw [integral_finsetSum _ (fun i _ => (hI i).const_mul _)]
      simp only [integral_const_mul]
    _ = _ := by
      have hmoment (i : ι) : (∫ x, F x i ^ r ∂μ) =
          Real.exp ((r ^ 2 - r) * V / 2) := by
        simp_rw [F, ← Real.exp_mul]
        simpa only [X, V, mul_comm] using
          integral_exp_subSquareComparison_normalized_mul hh γ hR hδ piece pt i (hc i) (hpt i) r
      simp_rw [hmoment, ← Finset.sum_mul, ha1, one_mul]
      rfl

/-- The moment of a finite atomic comparison mass is bounded by the
power of its total weight times the one-point moment. -/
theorem integral_rpow_sum_subSquareComparison_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (piece : ι → Fin 2) (pt : ι → ℂ)
    (hc : ∀ i, ‖LatticeProb.LQG.lqgSquareCentre (piece i)‖ + R ≤ 1)
    (hpt : ∀ i, ‖pt i‖ + δ ≤ 1) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {r : ℝ} (hr : 1 ≤ r) :
    (∫ x, (∑ i, a i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i -
        γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)) ^ r
      ∂(LatticeProb.Gauss.subSquareMeasure P)) ≤
    (∑ i, a i) ^ r *
      Real.exp ((r ^ 2 - r) * (γ ^ 2 * (1 - Real.log R - Real.log δ)) / 2) := by
  classical
  let M := ∑ i, a i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => ha i)
  rcases hM.eq_or_lt with hzero | hpos
  · have ha0 (i : ι) : a i = 0 := by
      have hi : a i ≤ M := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
      exact le_antisymm (by simpa [← hzero] using hi) (ha i)
    simp [ha0, Real.zero_rpow (by linarith : r ≠ 0)]
  · let b : ι → ℝ := fun i => a i / M
    have hb (i : ι) : 0 ≤ b i := div_nonneg (ha i) hpos.le
    have hb1 : ∑ i, b i = 1 := by
      simp only [b, ← Finset.sum_div]
      exact div_self (ne_of_gt hpos)
    have hn := integral_rpow_sum_subSquareComparison_le_of_sum_eq_one hh γ hR hδ piece pt hc hpt b hb hb1 hr
    have hscale (x : (Ω × ℝ) × (Fin 2 → Ω)) :
        (∑ i, a i * Real.exp
          (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i -
            γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)) ^ r =
        M ^ r * (∑ i, b i * Real.exp
          (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i -
            γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)) ^ r := by
      have heq : (∑ i, a i * Real.exp
          (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i -
            γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)) =
          M * (∑ i, b i * Real.exp
          (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i -
            γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [b]
        field_simp
      rw [heq, Real.mul_rpow hpos.le (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (hb i) (Real.exp_pos _).le))]
    simp_rw [hscale, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hM _)
/-- A finite atomic mass of the field has an explicit moment bound. -/
theorem integral_rpow_sum_subSquareField_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (piece : ι → Fin 2) (pt : ι → ℂ)
    (hpt : ∀ i, pt i ∈ LatticeProb.LQG.lqgSquare)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {r : ℝ} (hr : 1 ≤ r) :
    (∫ ω, (∑ i, a i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) piece pt ω i -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)) ^ r ∂P) ≤
    (∑ i, a i) ^ r * Real.exp ((r ^ 2 - r) *
      (γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ)) / 2) := by
  have hR := LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k
  have hc : ∀ i, ‖LatticeProb.LQG.lqgSquareCentre (piece i)‖ +
      LatticeProb.LQG.dyadicScale k ≤ 1 := fun i =>
    LatticeProb.LQG.norm_lqgSquareCentre_add_dyadicScale_le_one hk (piece i)
  have hn : ∀ i, ‖pt i‖ + δ ≤ 1 := fun i => by
    have hi : ‖pt i‖ ≤ 1 / 4 := by
      simpa using LatticeProb.LQG.lqgSquare_subset_closedBall (hpt i)
    linarith
  exact (integral_rpow_subSquareField_le_explicit_nonneg hh γ hk hδ hδ2 piece pt hpt ha hr).trans
    (integral_rpow_sum_subSquareComparison_le hh γ hR hδ piece pt hc hn a ha hr)


/-- A positive power of a finite nonnegative sum of lognormal variables is integrable. -/
theorem integrable_rpow_sum_exp_gaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} [Fintype ι] (X : ι → Ω → ℝ)
    (hX : ∀ i, HasGaussianLaw (X i) P) (a v : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun ω => (∑ i, a i * Real.exp (X i ω - v i)) ^ r) P := by
  classical
  let F : ι → Ω → ℝ := fun i ω => a i * Real.exp (X i ω - v i)
  have hF (i : ι) : AEStronglyMeasurable (F i) P :=
    ((hX i).aemeasurable.sub aemeasurable_const).exp.aestronglyMeasurable.const_mul _
  have hI (i : ι) : Integrable (fun ω => ‖F i ω‖ ^ r) P := by
    have hL : HasLaw (X i) (gaussianReal (∫ ω, X i ω ∂P) (variance (X i) P).toNNReal) P :=
      ⟨(hX i).aemeasurable, (hX i).map_eq_gaussianReal⟩
    have hi := hL.integrable_comp (f := fun y : ℝ => Real.exp (r * y))
      (integrable_exp_mul_gaussianReal r)
    have heq : (fun ω => ‖F i ω‖ ^ r) =
        (fun ω => (a i ^ r * Real.exp (-(r * v i))) * Real.exp (r * X i ω)) := by
      funext ω
      dsimp [F]
      rw [abs_of_nonneg (mul_nonneg (ha i) (Real.exp_pos _).le),
        Real.mul_rpow (ha i) (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring
    rw [heq]
    exact hi.const_mul _
  have hM (i : ι) : MemLp (F i) (ENNReal.ofReal r) P := by
    apply (integrable_norm_rpow_iff (hF i) (by simp [hr]) (by simp)).1
    simpa [ENNReal.toReal_ofReal hr.le] using hI i
  have hsum : MemLp (fun ω => ∑ i, F i ω) (ENNReal.ofReal r) P := by
    exact memLp_finsetSum Finset.univ (fun i _ => hM i)
  have := hsum.integrable_norm_rpow (by simp [hr]) (by simp)
  simpa only [ENNReal.toReal_ofReal hr.le, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (Real.exp_pos _).le)), F] using this

/-- Positive powers of finite atomic masses of the field are integrable. -/
theorem integrable_rpow_sum_subSquareField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R ε : ℝ} (hε : 0 < ε) (piece : ι → Fin 2) (pt : ι → ℂ)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (v : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun ω => (∑ i, a i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc R ε piece pt ω i - v i)) ^ r) P := by
  apply integrable_rpow_sum_exp_gaussian (fun i ω =>
    LatticeProb.Gauss.subSquareField γ hcirc R ε piece pt ω i) _ a v ha hr
  intro i
  exact (hh.hasGaussianLaw_subSquareField γ hε piece pt).eval i

/-- Positive powers of finite atomic masses of the comparison field are integrable. -/
theorem integrable_rpow_sum_subSquareComparison {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ι : Type*} [Fintype ι]
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (piece : ι → Fin 2) (pt : ι → ℂ)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (v : ι → ℝ) {r : ℝ} (hr : 0 < r) :
    Integrable (fun x => (∑ i, a i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i - v i)) ^ r)
      (LatticeProb.Gauss.subSquareMeasure P) := by
  apply integrable_rpow_sum_exp_gaussian (fun i x =>
    LatticeProb.Gauss.subSquareComparison γ hcirc R δ piece pt x i) _ a v ha hr
  intro i
  exact (hh.hasGaussianLaw_subSquareComparison γ hR hδ piece pt).eval i

private theorem uniformIntegrable_of_bounded_two {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (F : ι → Ω → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) P)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (F i) 2 P ≤ C) :
    UniformIntegrable F 1 P := by
  have hbound (i : ι) (s : Set Ω) (hs : MeasurableSet s) :
      eLpNorm (F i) 1 (P.restrict s) ≤ (C : ℝ≥0∞) * (P s) ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (by norm_num) ((hF i).restrict (s := s))
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div, inv_one,
      show (1 : ℝ) - (2 : ℝ)⁻¹ = 1 / 2 by norm_num, Measure.restrict_apply_univ] at h
    have h2 : eLpNorm (F i) 1 (P.restrict s) ≤
        eLpNorm (F i) 2 (P.restrict s) * (P s) ^ (1 / 2 : ℝ) := by
      convert h using 1
      norm_num
    refine h2.trans ?_
    gcongr
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hC i)
  have ht : Tendsto (fun t : ℝ≥0∞ => (C : ℝ≥0∞) * t ^ (1 / 2 : ℝ)) (𝓝 0) (𝓝 0) :=
    ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos ENNReal.coe_ne_top (by norm_num)
  refine ⟨unifIntegrable_iff'.2 ?_, ⟨C, ?_⟩⟩
  · intro ε hε
    have he := (ENNReal.tendsto_nhds_zero.1 ht) ε hε
    rw [ENNReal.nhds_zero_basis_Iic.eventually_iff] at he
    obtain ⟨δ, hδ, hδbound⟩ := he
    exact ⟨δ, hδ, fun i s hs hsδ => (hbound i s hs).trans (hδbound hsδ)⟩
  · intro i
    simpa only [measure_univ, ENNReal.one_rpow, mul_one, Measure.restrict_univ] using hbound i Set.univ MeasurableSet.univ

private theorem eLpNorm_two_le_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : Ω → ℝ) (hF : AEStronglyMeasurable F P)
    (hF0 : ∀ ω, 0 ≤ F ω) (hFi : Integrable (fun ω => F ω ^ 2) P)
    (K : ℝ) (hK : (∫ ω, F ω ^ 2 ∂P) ≤ K) :
    eLpNorm F 2 P ≤ (ENNReal.ofReal K) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hF]
  simp only [ENNReal.toReal_ofNat]
  have heq : (∫⁻ ω, ‖F ω‖ₑ ^ (2 : ℝ) ∂P) = ENNReal.ofReal (∫ ω, F ω ^ 2 ∂P) := by
    rw [ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    apply lintegral_congr
    intro ω
    rw [Real.enorm_eq_ofReal (hF0 ω), ENNReal.rpow_two, ← ENNReal.ofReal_pow (hF0 ω)]
  rw [heq]
  gcongr

/-- Powers of normalized finite atomic field masses form a uniformly integrable
family when their total weights are uniformly bounded at a fixed smoothing scale. -/
theorem uniformIntegrable_rpow_sum_subSquareField {Ω J : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (ι : J → Type*) [∀ j, Fintype (ι j)] (piece : ∀ j, ι j → Fin 2)
    (pt : ∀ j, ι j → ℂ) (hpt : ∀ j i, pt j i ∈ LatticeProb.LQG.lqgSquare)
    (a : ∀ j, ι j → ℝ) (ha : ∀ j i, 0 ≤ a j i)
    (M : ℝ) (hmass : ∀ j, ∑ i, a j i ≤ M)
    {q : ℝ} (hq : 1 ≤ q) :
    UniformIntegrable (fun j ω => (∑ i, a j i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) (piece j) (pt j) ω i -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)) ^ q) 1 P := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X : J → Ω → ℝ := fun j ω => ∑ i, a j i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) (piece j) (pt j) ω i -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)
  let K : ℝ := M ^ (2*q) * Real.exp (((2*q) ^ 2 - 2*q) *
      (γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ)) / 2)
  have hX0 (j ω) : 0 ≤ X j ω := Finset.sum_nonneg (fun i _ => mul_nonneg (ha j i) (Real.exp_pos _).le)
  have hI (j) (r : ℝ) (hr : 0 < r) : Integrable (fun ω => X j ω ^ r) P :=
    HarmonicBalls.integrable_rpow_sum_subSquareField hh γ
      (mul_pos (LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k) hδ) (piece j) (pt j)
      (a j) (ha j) (fun _ => γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2) hr
  have hsq (j) : Integrable (fun ω => (X j ω ^ q) ^ 2) P := by
    convert hI j (2*q) (by linarith) using 1
    funext ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hX0 j ω)]
    congr 1
    ring
  have hbound (j) : (∫ ω, (X j ω ^ q) ^ 2 ∂P) ≤ K := by
    have hh' := HarmonicBalls.integral_rpow_sum_subSquareField_le hh γ hk hδ hδ2
      (piece j) (pt j) (hpt j) (a j) (ha j) (r := 2*q) (by linarith)
    change (∫ ω, X j ω ^ (2*q) ∂P) ≤ _ at hh'
    calc
      _ = ∫ ω, X j ω ^ (2*q) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hX0 j ω)]
        congr 1
        ring
      _ ≤ _ := hh'
      _ ≤ K := by
        dsimp [K]
        gcongr
        · exact Finset.sum_nonneg (fun i _ => ha j i)
        · exact hmass j
  let D : ℝ≥0∞ := (ENNReal.ofReal K) ^ (1 / 2 : ℝ)
  have hD : D ≠ ∞ := by dsimp [D]; finiteness
  refine uniformIntegrable_of_bounded_two _ (fun j => (hI j q (by linarith)).aestronglyMeasurable)
      D.toNNReal (fun j => ?_)
  rw [ENNReal.coe_toNNReal hD]
  exact eLpNorm_two_le_of_integral_sq_le (fun ω => X j ω ^ q)
    (hI j q (by linarith)).aestronglyMeasurable (fun ω => Real.rpow_nonneg (hX0 j ω) q)
    (hsq j) K (hbound j)

/-- Powers of normalized finite atomic comparison masses form a uniformly
integrable family when their total weights are uniformly bounded at fixed scales. -/
theorem uniformIntegrable_rpow_sum_subSquareComparison {Ω J : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (ι : J → Type*) [∀ j, Fintype (ι j)] (piece : ∀ j, ι j → Fin 2)
    (pt : ∀ j, ι j → ℂ) (hpt : ∀ j i, pt j i ∈ LatticeProb.LQG.lqgSquare)
    (a : ∀ j, ι j → ℝ) (ha : ∀ j i, 0 ≤ a j i)
    (M : ℝ) (hmass : ∀ j, ∑ i, a j i ≤ M)
    {q : ℝ} (hq : 1 ≤ q) :
    UniformIntegrable (fun j ω => (∑ i, a j i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc (LatticeProb.LQG.dyadicScale k) δ (piece j) (pt j) ω i -
        γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2)) ^ q) 1 (LatticeProb.Gauss.subSquareMeasure P) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := LatticeProb.Gauss.subSquareMeasure P
  let X : J → ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun j ω => ∑ i, a j i * Real.exp
      (LatticeProb.Gauss.subSquareComparison γ hcirc (LatticeProb.LQG.dyadicScale k) δ (piece j) (pt j) ω i -
        γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2)
  let K : ℝ := M ^ (2*q) * Real.exp (((2*q) ^ 2 - 2*q) *
      (γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ)) / 2)
  have hX0 (j ω) : 0 ≤ X j ω := Finset.sum_nonneg (fun i _ => mul_nonneg (ha j i) (Real.exp_pos _).le)
  have hI (j) (r : ℝ) (hr : 0 < r) : Integrable (fun ω => X j ω ^ r) μ :=
    HarmonicBalls.integrable_rpow_sum_subSquareComparison hh γ
      (LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k) hδ (piece j) (pt j)
      (a j) (ha j) (fun _ => γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2) hr
  have hsq (j) : Integrable (fun ω => (X j ω ^ q) ^ 2) μ := by
    convert hI j (2*q) (by linarith) using 1
    funext ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hX0 j ω)]
    congr 1
    ring
  have hbound (j) : (∫ ω, (X j ω ^ q) ^ 2 ∂μ) ≤ K := by
    have hc : ∀ i, ‖LatticeProb.LQG.lqgSquareCentre (piece j i)‖ +
        LatticeProb.LQG.dyadicScale k ≤ 1 := fun i =>
      LatticeProb.LQG.norm_lqgSquareCentre_add_dyadicScale_le_one hk (piece j i)
    have hp : ∀ i, ‖pt j i‖ + δ ≤ 1 := fun i => by
      have hi : ‖pt j i‖ ≤ 1 / 4 := by
        simpa using LatticeProb.LQG.lqgSquare_subset_closedBall (hpt j i)
      linarith
    have hh' := HarmonicBalls.integral_rpow_sum_subSquareComparison_le hh γ
      (LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k) hδ
      (piece j) (pt j) hc hp (a j) (ha j) (r := 2*q) (by linarith)
    change (∫ ω, X j ω ^ (2*q) ∂μ) ≤ _ at hh'
    calc
      _ = ∫ ω, X j ω ^ (2*q) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hX0 j ω)]
        congr 1
        ring
      _ ≤ _ := hh'
      _ ≤ K := by
        dsimp [K]
        gcongr
        · exact Finset.sum_nonneg (fun i _ => ha j i)
        · exact hmass j
  let D : ℝ≥0∞ := (ENNReal.ofReal K) ^ (1 / 2 : ℝ)
  have hD : D ≠ ∞ := by dsimp [D]; finiteness
  refine uniformIntegrable_of_bounded_two _ (fun j => (hI j q (by linarith)).aestronglyMeasurable)
      D.toNNReal (fun j => ?_)
  rw [ENNReal.coe_toNNReal hD]
  exact eLpNorm_two_le_of_integral_sq_le (fun ω => X j ω ^ q)
    (hI j q (by linarith)).aestronglyMeasurable (fun ω => Real.rpow_nonneg (hX0 j ω) q)
    (hsq j) K (hbound j)

end HarmonicBalls
