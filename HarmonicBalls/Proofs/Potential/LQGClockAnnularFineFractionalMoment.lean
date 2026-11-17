import HarmonicBalls.Proofs.Potential.LQGClockAnnularCoarseCellMoment
import HarmonicBalls.Proofs.Sec6.BrownianScaling
import LatticeProb.LQG.LQGMassMoment
import LatticeProb.LQG.LQGMassSquares
import LatticeProb.LQG.LQGSubSquareGaussian
import LatticeProb.LQG.LQGSubSquareLimit
import LatticeProb.Prob.GaussKahaneRpow
import LatticeProb.Prob.GaussKahane2Const
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Fine-scale moments of inserted circle averages

The moment of the inserted density at a point has an explicit dependence on
its smoothing scale and the insertion point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal Topology
open Filter
open HarmonicBalls.Section6

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

/-- Almost-sure limits of bounded-mass atomic approximations preserve the
positive-moment comparison at fixed scales. -/
theorem integral_rpow_subSquareField_le_of_ae_atomic_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (piece : ∀ n, ι n → Fin 2)
    (pt : ∀ n, ι n → ℂ) (hpt : ∀ n i, pt n i ∈ LatticeProb.LQG.lqgSquare)
    (a : ∀ n, ι n → ℝ) (ha : ∀ n i, 0 ≤ a n i)
    (M : ℝ) (hmass : ∀ n, ∑ i, a n i ≤ M)
    {q : ℝ} (hq : 1 ≤ q) (F : Ω → ℝ)
    (G : ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ)
    (hF : ∀ᵐ ω ∂P, Tendsto (fun n => ∑ i, a n i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) (piece n) (pt n) ω i -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)) atTop (𝓝 (F ω)))
    (hG : ∀ᵐ x ∂(LatticeProb.Gauss.subSquareMeasure P), Tendsto (fun n => ∑ i,
      a n i * Real.exp (LatticeProb.Gauss.subSquareComparison γ hcirc
        (LatticeProb.LQG.dyadicScale k) δ (piece n) (pt n) x i -
        γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2))
      atTop (𝓝 (G x))) :
    Integrable (fun ω => F ω ^ q) P ∧
      Integrable (fun x => G x ^ q) (LatticeProb.Gauss.subSquareMeasure P) ∧
      (∫ ω, F ω ^ q ∂P) ≤ ∫ x, G x ^ q ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let X : ℕ → Ω → ℝ := fun n ω => (∑ i, a n i * Real.exp
      (LatticeProb.Gauss.subSquareField γ hcirc (LatticeProb.LQG.dyadicScale k)
        (LatticeProb.LQG.dyadicScale k * δ) (piece n) (pt n) ω i -
        γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)) ^ q
  let Y : ℕ → ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun n x => (∑ i,
      a n i * Real.exp (LatticeProb.Gauss.subSquareComparison γ hcirc
        (LatticeProb.LQG.dyadicScale k) δ (piece n) (pt n) x i -
        γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2)) ^ q
  have hUIX : UniformIntegrable X 1 P :=
    uniformIntegrable_rpow_sum_subSquareField hh γ hk hδ hδ2 ι piece pt hpt a ha M hmass hq
  have hUIY : UniformIntegrable Y 1 (LatticeProb.Gauss.subSquareMeasure P) :=
    uniformIntegrable_rpow_sum_subSquareComparison hh γ hk hδ hδ2 ι piece pt hpt a ha M hmass hq
  have hFX : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (F ω ^ q)) := by
    filter_upwards [hF] with ω hω
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ q)).continuousAt.tendsto.comp hω
  have hGY : ∀ᵐ x ∂(LatticeProb.Gauss.subSquareMeasure P),
      Tendsto (fun n => Y n x) atTop (𝓝 (G x ^ q)) := by
    filter_upwards [hG] with x hx
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ q)).continuousAt.tendsto.comp hx
  have hFi := hUIX.integrable_of_ae_tendsto hFX
  have hGi := hUIY.integrable_of_ae_tendsto hGY
  have hXL := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl (by simp)
    (fun n => hUIX.aestronglyMeasurable n) (memLp_one_iff_integrable.mpr hFi) hUIX.1 hFX
  have hYL := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl (by simp)
    (fun n => hUIY.aestronglyMeasurable n) (memLp_one_iff_integrable.mpr hGi) hUIY.1 hGY
  have hXI := tendsto_integral_of_L1' (fun ω => F ω ^ q)
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hUIX.memLp n))) hXL
  have hYI := tendsto_integral_of_L1' (fun x => G x ^ q)
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hUIY.memLp n))) hYL
  refine ⟨hFi, hGi, le_of_tendsto_of_tendsto hXI hYI ?_⟩
  exact Eventually.of_forall (fun n =>
    integral_rpow_subSquareField_le_explicit_nonneg hh γ hk hδ hδ2
      (piece n) (pt n) (hpt n) (ha n) hq)

/-- A deterministic quadrature approximation for continuous tests yields the
fixed-scale comparison for the corresponding integrals against both fields. -/
theorem integral_rpow_subSquareField_le_of_quadrature
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (piece : ∀ n, ι n → Fin 2)
    (pt : ∀ n, ι n → ℂ) (hpt : ∀ n i, pt n i ∈ LatticeProb.LQG.lqgSquare)
    (a : ∀ n, ι n → ℝ) (ha : ∀ n i, 0 ≤ a n i)
    (M : ℝ) (hmass : ∀ n, ∑ i, a n i ≤ M)
    (ν : Fin 2 → Measure ℂ)
    (hquad : ∀ f : Fin 2 → ℂ → ℝ, (∀ s, Continuous (f s)) →
      Tendsto (fun n => ∑ i, a n i * f (piece n i) (pt n i)) atTop
        (𝓝 (∑ s, ∫ z, f s z ∂(ν s))))
    {q : ℝ} (hq : 1 ≤ q) :
    let R := LatticeProb.LQG.dyadicScale k
    let F : Ω → ℝ := fun ω => ∑ s, ∫ z, Real.exp
      (γ * hcirc ω (R * δ) ((R : ℂ) * z + LatticeProb.LQG.lqgSquareCentre s) -
        γ ^ 2 * (-Real.log (R * δ)) / 2) ∂(ν s)
    let G : ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun x => ∑ s, ∫ z, Real.exp
      (γ * (hcirc x.1.1 R (LatticeProb.LQG.lqgSquareCentre s) + hcirc (x.2 s) δ z + x.1.2) -
        γ ^ 2 * (1 - Real.log R - Real.log δ) / 2) ∂(ν s)
    Integrable (fun ω => F ω ^ q) P ∧
      Integrable (fun x => G x ^ q) (LatticeProb.Gauss.subSquareMeasure P) ∧
      (∫ ω, F ω ^ q ∂P) ≤ ∫ x, G x ^ q ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hR := LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k
  have hε : 0 < LatticeProb.LQG.dyadicScale k * δ := mul_pos hR hδ
  apply integral_rpow_subSquareField_le_of_ae_atomic_tendsto hh γ hk hδ hδ2 ι piece pt hpt a ha M hmass hq
  · filter_upwards [hh.ae_continuous_circle_fixed hε] with ω hω
    have htest : ∀ s : Fin 2, Continuous (fun z : ℂ => Real.exp
        (γ * hcirc ω (LatticeProb.LQG.dyadicScale k * δ)
          ((LatticeProb.LQG.dyadicScale k : ℂ) * z + LatticeProb.LQG.lqgSquareCentre s) -
          γ ^ 2 * (-Real.log (LatticeProb.LQG.dyadicScale k * δ)) / 2)) := by
      intro s
      fun_prop
    simpa only [LatticeProb.Gauss.subSquareField] using hquad _ htest
  · have hae : ∀ᵐ x ∂(LatticeProb.Gauss.subSquareMeasure P), ∀ s : Fin 2,
        Continuous (hcirc (x.2 s) δ) := by
      rw [ae_all_iff]
      intro s
      exact (LatticeProb.Gauss.measurePreserving_subSquare_eval s).quasiMeasurePreserving.ae
        (hh.ae_continuous_circle_fixed hδ)
    filter_upwards [hae] with x hx
    have htest : ∀ s : Fin 2, Continuous (fun z : ℂ => Real.exp
        (γ * (hcirc x.1.1 (LatticeProb.LQG.dyadicScale k) (LatticeProb.LQG.lqgSquareCentre s) +
          hcirc (x.2 s) δ z + x.1.2) -
          γ ^ 2 * (1 - Real.log (LatticeProb.LQG.dyadicScale k) - Real.log δ) / 2)) := by
      intro s
      fun_prop
    simpa only [LatticeProb.Gauss.subSquareComparison] using hquad _ htest

/-- Finite-valued approximations converge under continuous tests and finite measures. -/
theorem tendsto_integral_comp_approxOn {K : Set ℂ} (hK : IsCompact K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ K) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ K) (f : ℂ → ℝ) (hf : Continuous f) :
    Tendsto (fun n => ∫ z, f (SimpleFunc.approxOn id measurable_id K z₀ hz₀ n z) ∂μ)
      atTop (𝓝 (∫ z, f z ∂μ)) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  apply tendsto_integral_of_dominated_convergence (fun _ => C)
  · intro n
    exact (hf.measurable.comp (SimpleFunc.approxOn id measurable_id K z₀ hz₀ n).measurable).aestronglyMeasurable
  · exact integrable_const C
  · intro n
    exact ae_of_all _ (fun z => hC _ (SimpleFunc.approxOn_mem measurable_id hz₀ n z))
  · filter_upwards [hμ] with z hz
    exact hf.continuousAt.tendsto.comp (SimpleFunc.tendsto_approxOn measurable_id hz₀ (subset_closure hz))

/-- Integrating a function of a simple map is a sum over its fibers. -/
theorem integral_comp_simple_eq_sum {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] (T : SimpleFunc α ℂ) (hT : Integrable T μ)
    (f : ℂ → ℝ) (hf : Integrable (fun x => f (T x)) μ) :
    (∫ x, f (T x) ∂μ) = ∑ z ∈ T.range, μ.real (T ⁻¹' {z}) * f z := by
  classical
  have hmass : (∑ z ∈ T.range, μ.real (T ⁻¹' {z})) = μ.real univ := by
    simp only [measureReal_def, ← ENNReal.toReal_sum (fun z _ => measure_ne_top μ _),
      T.sum_range_measure_preimage_singleton]
  let g : ℂ → ℝ := fun z => f z - f 0
  have hg0 : g 0 = 0 := sub_self _
  have hgi : Integrable (T.map g) μ := by
    change Integrable (fun x => f (T x) - f 0) μ
    exact hf.sub (integrable_const (f 0))
  have hgi' : Integrable (fun x => g (T x)) μ := hgi
  have hsum := T.map_integral g hT hg0
  rw [SimpleFunc.integral_eq_integral _ hgi] at hsum
  change (∫ x, g (T x) ∂μ) = _ at hsum
  have heq : (∫ x, f (T x) ∂μ) = (∫ x, g (T x) ∂μ) + μ.real univ * f 0 := by
    calc
      (∫ x, f (T x) ∂μ) = ∫ x, (g (T x) + f 0) ∂μ := by simp only [g, sub_add_cancel]
      _ = (∫ x, g (T x) ∂μ) + μ.real univ * f 0 := by
        rw [integral_add hgi' (integrable_const _), integral_const]
        rfl
  rw [heq, hsum]
  simp only [g, smul_eq_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass]
  ring

/-- Fiber-mass quadrature converges for continuous tests on a compact set. -/
theorem tendsto_sum_fiber_mass_mul {K : Set ℂ} (hK : IsCompact K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ K) (μ : Measure ℂ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, z ∈ K) (f : ℂ → ℝ) (hf : Continuous f) :
    let T := fun n => SimpleFunc.approxOn id measurable_id K z₀ hz₀ n
    Tendsto (fun n => ∑ z ∈ (T n).range, μ.real ((T n) ⁻¹' {z}) * f z)
      atTop (𝓝 (∫ z, f z ∂μ)) := by
  dsimp only
  have hconv := tendsto_integral_comp_approxOn hK hz₀ μ hμ f hf
  convert hconv using 1
  ext n
  let T := SimpleFunc.approxOn id measurable_id K z₀ hz₀ n
  obtain ⟨C, hC⟩ := hK.isBounded.exists_norm_le
  have hTi : Integrable T μ := Integrable.of_bound T.stronglyMeasurable.aestronglyMeasurable C
    (ae_of_all _ (fun z => hC _ (SimpleFunc.approxOn_mem measurable_id hz₀ n z)))
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  have hFi : Integrable (fun z => f (T z)) μ := Integrable.of_bound
    (hf.measurable.comp T.measurable).aestronglyMeasurable D
    (ae_of_all _ (fun z => hD _ (SimpleFunc.approxOn_mem measurable_id hz₀ n z)))
  exact (integral_comp_simple_eq_sum μ T hTi f hFi).symm

/-- Fiber-mass quadrature converges simultaneously for two finite measures. -/
theorem tendsto_sum_fiber_mass_mul_pair {K : Set ℂ} (hK : IsCompact K)
    {z₀ : ℂ} (hz₀ : z₀ ∈ K) (ν : Fin 2 → Measure ℂ)
    [∀ s, IsFiniteMeasure (ν s)] (hν : ∀ s, ∀ᵐ z ∂(ν s), z ∈ K)
    (f : Fin 2 → ℂ → ℝ) (hf : ∀ s, Continuous (f s)) :
    let T := fun n => SimpleFunc.approxOn id measurable_id K z₀ hz₀ n
    Tendsto (fun n => ∑ i : Fin 2 × ↥(T n).range,
      (ν i.1).real ((T n) ⁻¹' {i.2.1}) * f i.1 i.2.1)
      atTop (𝓝 (∑ s, ∫ z, f s z ∂(ν s))) := by
  dsimp only
  have hconv : ∀ s : Fin 2, Tendsto (fun n => ∑ z ∈
      (SimpleFunc.approxOn id measurable_id K z₀ hz₀ n).range,
      (ν s).real ((SimpleFunc.approxOn id measurable_id K z₀ hz₀ n) ⁻¹' {z}) * f s z)
      atTop (𝓝 (∫ z, f s z ∂(ν s))) := fun s =>
    tendsto_sum_fiber_mass_mul hK hz₀ (ν s) (hν s) (f s) (hf s)
  have hsum := tendsto_finsetSum Finset.univ (fun s _ => hconv s)
  convert hsum using 1
  ext n
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  change (∑ y : ↥(SimpleFunc.approxOn id measurable_id K z₀ hz₀ n).range,
    (ν s).real ((SimpleFunc.approxOn id measurable_id K z₀ hz₀ n) ⁻¹' {y.1}) * f s y.1) = _
  exact Finset.sum_coe_sort (SimpleFunc.approxOn id measurable_id K z₀ hz₀ n).range
    (fun z : ℂ => (ν s).real ((SimpleFunc.approxOn id measurable_id K z₀ hz₀ n) ⁻¹' {z}) * f s z)

/-- Fixed-scale comparison for two finite measures carried by the reference square. -/
theorem integral_rpow_subSquareField_le_of_finite_measures
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (ν : Fin 2 → Measure ℂ) [∀ s, IsFiniteMeasure (ν s)]
    (hν : ∀ s, ∀ᵐ z ∂(ν s), z ∈ LatticeProb.LQG.lqgSquare)
    {q : ℝ} (hq : 1 ≤ q) :
    let R := LatticeProb.LQG.dyadicScale k
    let F : Ω → ℝ := fun ω => ∑ s, ∫ z, Real.exp
      (γ * hcirc ω (R * δ) ((R : ℂ) * z + LatticeProb.LQG.lqgSquareCentre s) -
        γ ^ 2 * (-Real.log (R * δ)) / 2) ∂(ν s)
    let G : ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun x => ∑ s, ∫ z, Real.exp
      (γ * (hcirc x.1.1 R (LatticeProb.LQG.lqgSquareCentre s) + hcirc (x.2 s) δ z + x.1.2) -
        γ ^ 2 * (1 - Real.log R - Real.log δ) / 2) ∂(ν s)
    Integrable (fun ω => F ω ^ q) P ∧
      Integrable (fun x => G x ^ q) (LatticeProb.Gauss.subSquareMeasure P) ∧
      (∫ ω, F ω ^ q ∂P) ≤ ∫ x, G x ^ q ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  classical
  have hK : IsCompact LatticeProb.LQG.lqgSquare := by
    have hc : IsClosed LatticeProb.LQG.lqgSquare := by
      have hre : Continuous fun w : ℂ => |w.re| := Complex.continuous_re.abs
      have him : Continuous fun w : ℂ => |w.im| := Complex.continuous_im.abs
      exact (isClosed_le hre continuous_const).inter (isClosed_le him continuous_const)
    exact (isCompact_closedBall (0 : ℂ) (1 / 4)).of_isClosed_subset hc
      LatticeProb.LQG.lqgSquare_subset_closedBall
  have h0 : (0 : ℂ) ∈ LatticeProb.LQG.lqgSquare := by
    simp [LatticeProb.LQG.lqgSquare]
  let T := fun n => SimpleFunc.approxOn id measurable_id LatticeProb.LQG.lqgSquare 0 h0 n
  let ι : ℕ → Type := fun n => Fin 2 × ↥(T n).range
  let piece : ∀ n, ι n → Fin 2 := fun _ i => i.1
  let pt : ∀ n, ι n → ℂ := fun _ i => i.2.1
  let a : ∀ n, ι n → ℝ := fun n i => (ν i.1).real ((T n) ⁻¹' {i.2.1})
  have hpt : ∀ n i, pt n i ∈ LatticeProb.LQG.lqgSquare := by
    intro n i
    obtain ⟨z, hz⟩ := SimpleFunc.mem_range.mp i.2.2
    change i.2.1 ∈ LatticeProb.LQG.lqgSquare
    rw [← hz]
    exact SimpleFunc.approxOn_mem measurable_id h0 n z
  have ha : ∀ n i, 0 ≤ a n i := fun _ _ => ENNReal.toReal_nonneg
  have hmass : ∀ n, ∑ i, a n i ≤ ∑ s, (ν s).real univ := by
    intro n
    rw [Fintype.sum_prod_type]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro s _
    change (∑ y : ↥(T n).range, (ν s).real ((T n) ⁻¹' {y.1})) = (ν s).real univ
    calc
      _ = ∑ z ∈ (T n).range, (ν s).real ((T n) ⁻¹' {z}) :=
        Finset.sum_coe_sort (T n).range (fun z : ℂ => (ν s).real ((T n) ⁻¹' {z}))
      _ = _ := by
        simp only [measureReal_def, ← ENNReal.toReal_sum (fun z _ => measure_ne_top (ν s) _),
          (T n).sum_range_measure_preimage_singleton]
  apply integral_rpow_subSquareField_le_of_quadrature hh γ hk hδ hδ2 ι piece pt hpt a ha
    (∑ s, (ν s).real univ) hmass ν ?_ hq
  intro f hf
  exact tendsto_sum_fiber_mass_mul_pair hK h0 ν hν f hf

/-- The rescaled occupation measure of a path in one comparison square. -/
noncomputable def subSquareOccupation (b : ContinuousPath ℂ) (u v R : ℝ) (s : Fin 2) :
    Measure ℂ :=
  let g : ℝ → ℂ := fun t => (b t.toNNReal - LatticeProb.LQG.lqgSquareCentre s) / R
  Measure.map g (volume.restrict (Ioc u v ∩ g ⁻¹' LatticeProb.LQG.lqgSquare))

instance (b : ContinuousPath ℂ) (u v R : ℝ) (s : Fin 2) :
    IsFiniteMeasure (subSquareOccupation b u v R s) := by
  dsimp [subSquareOccupation]
  let : IsFiniteMeasure (volume.restrict (Ioc u v ∩
      (fun t : ℝ => (b t.toNNReal - LatticeProb.LQG.lqgSquareCentre s) / R) ⁻¹'
        LatticeProb.LQG.lqgSquare)) :=
    isFiniteMeasure_of_le (volume.restrict (Ioc u v))
      (Measure.restrict_mono_set volume inter_subset_left)
  infer_instance

/-- Each rescaled occupation measure is carried by the reference square. -/
theorem ae_mem_subSquareOccupation (b : ContinuousPath ℂ) (u v R : ℝ) (s : Fin 2) :
    ∀ᵐ z ∂(subSquareOccupation b u v R s), z ∈ LatticeProb.LQG.lqgSquare := by
  let g : ℝ → ℂ := fun t => (b t.toNNReal - LatticeProb.LQG.lqgSquareCentre s) / R
  have hg : Continuous g := by
    dsimp [g]
    fun_prop
  have hQ : MeasurableSet LatticeProb.LQG.lqgSquare := by
    apply IsClosed.measurableSet
    have hre : Continuous fun w : ℂ => |w.re| := Complex.continuous_re.abs
    have him : Continuous fun w : ℂ => |w.im| := Complex.continuous_im.abs
    exact (isClosed_le hre continuous_const).inter (isClosed_le him continuous_const)
  change ∀ᵐ z ∂(Measure.map g (volume.restrict (Ioc u v ∩ g ⁻¹' LatticeProb.LQG.lqgSquare))),
    z ∈ LatticeProb.LQG.lqgSquare
  apply (ae_map_iff (p := fun z => z ∈ LatticeProb.LQG.lqgSquare)
    hg.measurable.aemeasurable hQ).2
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.inter (hg.measurable hQ))] with t ht
  exact ht.2

/-- Continuous tests against a rescaled occupation measure are time integrals. -/
theorem integral_subSquareOccupation (b : ContinuousPath ℂ) (u v R : ℝ) (s : Fin 2)
    (f : ℂ → ℝ) (hf : Continuous f) :
    ∫ z, f z ∂(subSquareOccupation b u v R s) =
      ∫ t in Ioc u v ∩ (fun t : ℝ => (b t.toNNReal -
        LatticeProb.LQG.lqgSquareCentre s) / R) ⁻¹' LatticeProb.LQG.lqgSquare,
        f ((b t.toNNReal - LatticeProb.LQG.lqgSquareCentre s) / R) := by
  apply integral_map
  · fun_prop
  · exact hf.aestronglyMeasurable

/-- Fixed-scale Gaussian comparison for two rescaled path occupation measures. -/
theorem integral_rpow_subSquareField_le_of_occupation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (b : ContinuousPath ℂ) (u v : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    let R := LatticeProb.LQG.dyadicScale k
    let ν := fun s => subSquareOccupation b u v R s
    let F : Ω → ℝ := fun ω => ∑ s, ∫ z, Real.exp
      (γ * hcirc ω (R * δ) ((R : ℂ) * z + LatticeProb.LQG.lqgSquareCentre s) -
        γ ^ 2 * (-Real.log (R * δ)) / 2) ∂(ν s)
    let G : ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun x => ∑ s, ∫ z, Real.exp
      (γ * (hcirc x.1.1 R (LatticeProb.LQG.lqgSquareCentre s) + hcirc (x.2 s) δ z + x.1.2) -
        γ ^ 2 * (1 - Real.log R - Real.log δ) / 2) ∂(ν s)
    Integrable (fun ω => F ω ^ q) P ∧
      Integrable (fun x => G x ^ q) (LatticeProb.Gauss.subSquareMeasure P) ∧
      (∫ ω, F ω ^ q ∂P) ≤ ∫ x, G x ^ q ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  exact integral_rpow_subSquareField_le_of_finite_measures hh γ hk hδ hδ2 _
    (fun s => ae_mem_subSquareOccupation b u v _ s) hq


/-- Fixed-scale comparison for the time spent in the two comparison squares. -/
theorem integral_rpow_subSquareField_le_of_time_integrals
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (b : ContinuousPath ℂ) (u v : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    let R := LatticeProb.LQG.dyadicScale k
    let g : Fin 2 → ℝ → ℂ := fun s t =>
      (b t.toNNReal - LatticeProb.LQG.lqgSquareCentre s) / R
    let I : Fin 2 → Set ℝ := fun s => Ioc u v ∩ g s ⁻¹' LatticeProb.LQG.lqgSquare
    let F : Ω → ℝ := fun ω => ∑ s, ∫ t in I s, Real.exp
      (γ * hcirc ω (R * δ) ((R : ℂ) * g s t + LatticeProb.LQG.lqgSquareCentre s) -
        γ ^ 2 * (-Real.log (R * δ)) / 2)
    let G : ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun x => ∑ s, ∫ t in I s, Real.exp
      (γ * (hcirc x.1.1 R (LatticeProb.LQG.lqgSquareCentre s) + hcirc (x.2 s) δ (g s t) + x.1.2) -
        γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)
    Integrable (fun ω => F ω ^ q) P ∧
      Integrable (fun x => G x ^ q) (LatticeProb.Gauss.subSquareMeasure P) ∧
      (∫ ω, F ω ^ q ∂P) ≤ ∫ x, G x ^ q ∂(LatticeProb.Gauss.subSquareMeasure P) := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let R := LatticeProb.LQG.dyadicScale k
  let ν := fun s => subSquareOccupation b u v R s
  let g : Fin 2 → ℝ → ℂ := fun s t =>
    (b t.toNNReal - LatticeProb.LQG.lqgSquareCentre s) / R
  let I : Fin 2 → Set ℝ := fun s => Ioc u v ∩ g s ⁻¹' LatticeProb.LQG.lqgSquare
  let F : Ω → ℝ := fun ω => ∑ s, ∫ z, Real.exp
    (γ * hcirc ω (R * δ) ((R : ℂ) * z + LatticeProb.LQG.lqgSquareCentre s) -
      γ ^ 2 * (-Real.log (R * δ)) / 2) ∂(ν s)
  let G : ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun x => ∑ s, ∫ z, Real.exp
    (γ * (hcirc x.1.1 R (LatticeProb.LQG.lqgSquareCentre s) + hcirc (x.2 s) δ z + x.1.2) -
      γ ^ 2 * (1 - Real.log R - Real.log δ) / 2) ∂(ν s)
  let Ftime : Ω → ℝ := fun ω => ∑ s, ∫ t in I s, Real.exp
    (γ * hcirc ω (R * δ) ((R : ℂ) * g s t + LatticeProb.LQG.lqgSquareCentre s) -
      γ ^ 2 * (-Real.log (R * δ)) / 2)
  let Gtime : ((Ω × ℝ) × (Fin 2 → Ω)) → ℝ := fun x => ∑ s, ∫ t in I s, Real.exp
    (γ * (hcirc x.1.1 R (LatticeProb.LQG.lqgSquareCentre s) + hcirc (x.2 s) δ (g s t) + x.1.2) -
      γ ^ 2 * (1 - Real.log R - Real.log δ) / 2)
  have hε : 0 < R * δ := mul_pos (LatticeProb.LQG.LQGDyadicScaling.dyadicScale_pos' k) hδ
  have hF : F =ᵐ[P] Ftime := by
    filter_upwards [hh.ae_continuous_circle_fixed hε] with ω hω
    apply Finset.sum_congr rfl
    intro s _
    apply integral_subSquareOccupation
    fun_prop
  have hG : G =ᵐ[LatticeProb.Gauss.subSquareMeasure P] Gtime := by
    have hae : ∀ᵐ x ∂(LatticeProb.Gauss.subSquareMeasure P), ∀ s : Fin 2,
        Continuous (hcirc (x.2 s) δ) := by
      rw [ae_all_iff]
      intro s
      exact (LatticeProb.Gauss.measurePreserving_subSquare_eval s).quasiMeasurePreserving.ae
        (hh.ae_continuous_circle_fixed hδ)
    filter_upwards [hae] with x hx
    apply Finset.sum_congr rfl
    intro s _
    apply integral_subSquareOccupation
    fun_prop
  have h := integral_rpow_subSquareField_le_of_occupation hh γ hk hδ hδ2 b u v hq
  change Integrable (fun ω => F ω ^ q) P ∧
    Integrable (fun x => G x ^ q) (LatticeProb.Gauss.subSquareMeasure P) ∧
    (∫ ω, F ω ^ q ∂P) ≤ ∫ x, G x ^ q ∂(LatticeProb.Gauss.subSquareMeasure P) at h
  have hFq : (fun ω => F ω ^ q) =ᵐ[P] (fun ω => Ftime ω ^ q) := hF.mono (fun _ h => congrArg (fun z : ℝ => z ^ q) h)
  have hGq : (fun x => G x ^ q) =ᵐ[LatticeProb.Gauss.subSquareMeasure P]
      (fun x => Gtime x ^ q) := hG.mono (fun _ h => congrArg (fun z : ℝ => z ^ q) h)
  exact ⟨h.1.congr hFq, h.2.1.congr hGq, by
    rw [← integral_congr_ae hFq, ← integral_congr_ae hGq]
    exact h.2.2⟩

/-- A subcritical parameter admits a moment order with negative recursion exponent. -/
theorem exists_subcritical_clock_exponent {γ : ℝ} (hγ : γ ^ 2 < 4) :
    ∃ q : ℝ, 1 < q ∧ q < 2 ∧ 2 + (q ^ 2 * γ ^ 2 / 2 - q * (2 + γ ^ 2 / 2)) < 0 := by
  let a : ℝ := γ ^ 2
  let q : ℝ := 1 + (4 - a) / 8
  have ha0 : 0 ≤ a := sq_nonneg γ
  have ha4 : a < 4 := hγ
  have hq1 : 1 < q := by dsimp [q]; linarith
  have hq2 : q < 2 := by dsimp [q]; linarith
  have hmul : a * (q - 1) ≤ 4 * (q - 1) :=
    mul_le_mul_of_nonneg_right ha4.le (by linarith)
  have haq : a * q < 4 := by
    dsimp [q] at hmul ⊢
    nlinarith
  have hneg : a * q / 2 - 2 < 0 := by linarith
  have hprod := mul_neg_of_pos_of_neg (sub_pos.mpr hq1) hneg
  refine ⟨q, hq1, hq2, ?_⟩
  change 2 + (q ^ 2 * a / 2 - q * (2 + a / 2)) < 0
  nlinarith [hprod]

/-- A negative exponent makes the dyadic recursion coefficient arbitrarily small. -/
theorem exists_dyadic_rpow_contraction {e : ℝ} (he : e < 0) (C : ℝ) :
    ∃ m : ℕ, 4 ≤ m ∧ C * m * (2 : ℝ) ^ ((m : ℝ) * e) < 1 / 2 := by
  let b : ℝ := -e * Real.log 2
  have hb : 0 < b := mul_pos (neg_pos.mpr he) (Real.log_pos (by norm_num))
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hlim' : Tendsto (fun n : ℕ => C * n * (2 : ℝ) ^ ((n : ℝ) * e)) atTop (𝓝 0) := by
    have h := hlim.const_mul C
    simp only [Real.rpow_one, mul_zero] at h
    convert h using 1
    funext n
    simp only [Function.comp_apply]
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc]
    dsimp [b]
    congr 2
    ring
  have h := (tendsto_order.1 hlim').2 (1 / 2) (by norm_num)
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  exact ⟨max N 4, le_max_right _ _, hN _ (le_max_left _ _)⟩

/-- Separated occupation masses have a smoothing-uniform cross moment. -/
theorem lintegral_mul_separated_gmc_masses_le {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (x : X → ℂ) (y : Y → ℂ) (hxm : Measurable x) (hym : Measurable y)
    (hx : ∀ a, ‖x a‖ + ε ≤ 1) (hy : ∀ b, ‖y b‖ + ε ≤ 1)
    (hxy : ∀ a b, r ≤ ‖x a - y b‖) :
    (∫⁻ ω, (∫⁻ a, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (x a) ω) ∂μ) *
      (∫⁻ b, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (y b) ω) ∂ν) ∂P) ≤
      ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (μ Set.univ * ν Set.univ) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let D : ℂ → Ω → ℝ≥0∞ := LatticeProb.Gauss.gmcDensityENN (fun z ω => H ω ε z) γ ε
  have hD : Measurable (Function.uncurry D) :=
    LatticeProb.Gauss.measurable_uncurry_gmcDensityENN (hHm ε hε) γ ε
  have hpoint (z : ℂ) (hz : ‖z‖ + ε ≤ 1) : (∫⁻ ω, D z ω ∂P) = 1 := by
    have heq : (fun ω => D z ω) =ᵐ[P] (fun ω =>
        ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε z ω)) := by
      filter_upwards [hHae] with ω hω
      simp only [D, LatticeProb.Gauss.gmcDensityENN, LatticeProb.Gauss.gmcDensity, hω]
    rw [lintegral_congr_ae heq, ← ofReal_integral_eq_lintegral_ofReal]
    · change ENNReal.ofReal (∫ ω, ε ^ (γ ^ 2 / 2) * Real.exp (γ * hcirc ω ε z) ∂P) = 1
      rw [hh.integral_rpow_mul_exp_circle hε hz γ, ENNReal.ofReal_one]
    · simpa only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton] using
        hh.integrable_prod_gmcDensity hε γ (fun _ : Fin 1 => z)
    · exact Filter.Eventually.of_forall fun ω => LatticeProb.Gauss.gmcDensity_nonneg hcirc hε γ z ω
  have hFx : Measurable (Function.uncurry (fun a ω => D (x a) ω)) :=
    hD.comp (hxm.comp measurable_fst |>.prodMk measurable_snd)
  have hGy : Measurable (Function.uncurry (fun b ω => D (y b) ω)) :=
    hD.comp (hym.comp measurable_fst |>.prodMk measurable_snd)
  have hdec (a : X) (b : Y) : (∫⁻ ω, D (x a) ω * D (y b) ω ∂P) ≤
      ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        ((∫⁻ ω, D (x a) ω ∂P) * ∫⁻ ω, D (y b) ω ∂P) := by
    have h := hh.lintegral_prod_gmcDensityENN_two_le hε hr γ
      (fun z => hHae.mono (fun ω hω => hω ε z))
      (fun _ : Fin 1 => x a) (fun _ : Fin 1 => y b)
      (fun _ => hx a) (fun _ => hy b) (fun _ _ => hxy a b)
    simpa only [Finset.univ_unique, Fin.default_eq_zero, Finset.prod_singleton,
      Fintype.card_fin, one_mul, pow_one, D] using h
  have hmain := LatticeProb.lintegral_mul_lintegral_le_of_forall (P := P) (ν₁ := μ) (ν₂ := ν) hFx hGy
    (ENNReal.ofReal ((2 / r) ^ (γ ^ 2))) hdec
  have hleft : (∫⁻ ω, ∫⁻ a, D (x a) ω ∂μ ∂P) = μ Set.univ := by
    have hm : Measurable (Function.uncurry (fun ω a => D (x a) ω)) := hFx.comp measurable_swap
    rw [lintegral_lintegral_swap (μ := P) (ν := μ) hm.aemeasurable]
    simp only [hpoint _ (hx _), lintegral_one]
  have hright : (∫⁻ ω, ∫⁻ b, D (y b) ω ∂ν ∂P) = ν Set.univ := by
    have hm : Measurable (Function.uncurry (fun ω b => D (y b) ω)) := hGy.comp measurable_swap
    rw [lintegral_lintegral_swap (μ := P) (ν := ν) hm.aemeasurable]
    simp only [hpoint _ (hy _), lintegral_one]
  rw [hleft, hright] at hmain
  convert hmain using 1
  apply lintegral_congr_ae
  filter_upwards [hHae] with ω hω
  congr 1 <;> apply lintegral_congr <;> intro z <;>
    simp only [D, LatticeProb.Gauss.gmcDensityENN, LatticeProb.Gauss.gmcDensity, hω]

/-- Fractional cross moments of separated occupation masses are uniformly bounded. -/
theorem lintegral_rpow_mul_separated_gmc_masses_le {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (x : X → ℂ) (y : Y → ℂ) (hxm : Measurable x) (hym : Measurable y)
    (hx : ∀ a, ‖x a‖ + ε ≤ 1) (hy : ∀ b, ‖y b‖ + ε ≤ 1)
    (hxy : ∀ a b, r ≤ ‖x a - y b‖) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∫⁻ ω, ((∫⁻ a, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (x a) ω) ∂μ) *
      (∫⁻ b, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (y b) ω) ∂ν)) ^ (q / 2) ∂P) ≤
      (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (μ Set.univ * ν Set.univ)) ^ (q / 2) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let D : ℂ → Ω → ℝ≥0∞ := LatticeProb.Gauss.gmcDensityENN (fun z ω => H ω ε z) γ ε
  have hD : Measurable (Function.uncurry D) :=
    LatticeProb.Gauss.measurable_uncurry_gmcDensityENN (hHm ε hε) γ ε
  have hFx : Measurable (fun ω => ∫⁻ a, D (x a) ω ∂μ) := by
    have hm : Measurable (fun p : Ω × X => D (x p.2) p.1) :=
      hD.comp ((hxm.comp measurable_snd).prodMk measurable_fst)
    exact hm.lintegral_prod_right'
  have hGy : Measurable (fun ω => ∫⁻ b, D (y b) ω ∂ν) := by
    have hm : Measurable (fun p : Ω × Y => D (y p.2) p.1) :=
      hD.comp ((hym.comp measurable_snd).prodMk measurable_fst)
    exact hm.lintegral_prod_right'
  have ha : (fun ω => (∫⁻ a, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (x a) ω) ∂μ) *
      (∫⁻ b, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (y b) ω) ∂ν)) =ᵐ[P]
      (fun ω => (∫⁻ a, D (x a) ω ∂μ) * ∫⁻ b, D (y b) ω ∂ν) := by
    filter_upwards [hHae] with ω hω
    congr 1 <;> apply lintegral_congr <;> intro z <;>
      simp only [D, LatticeProb.Gauss.gmcDensityENN, LatticeProb.Gauss.gmcDensity, hω]
  have hm := (hFx.mul hGy).aemeasurable.congr ha.symm
  exact (LatticeProb.lintegral_rpow_le_rpow_lintegral P (by positivity : 0 < q / 2)
    (by linarith : q / 2 ≤ 1) hm).trans
      (ENNReal.rpow_le_rpow (lintegral_mul_separated_gmc_masses_le hh μ ν hε hr γ x y hxm hym hx hy hxy) (by positivity))

/-- Separated occupation masses are bounded using the volumes of their time sets. -/
theorem lintegral_rpow_mul_separated_time_masses_le_volume {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v : ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (hx : ∀ t ∈ A ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hy : ∀ t ∈ B ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hxy : ∀ t ∈ A ∩ Ioc u v, ∀ s ∈ B ∩ Ioc u v,
      r ≤ ‖b t.toNNReal - b s.toNNReal‖) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∫⁻ ω, ((∫⁻ t in A ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) *
      (∫⁻ t in B ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))) ^ (q / 2) ∂P) ≤
      (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        (volume (A ∩ Ioc u v) * volume (B ∩ Ioc u v))) ^ (q / 2) := by
  let S := A ∩ Ioc u v
  let T := B ∩ Ioc u v
  have hS : MeasurableSet S := hA.inter measurableSet_Ioc
  have hT : MeasurableSet T := hB.inter measurableSet_Ioc
  let μ : Measure S := (volume : Measure ℝ).comap Subtype.val
  let ν : Measure T := (volume : Measure ℝ).comap Subtype.val
  have hμ : μ Set.univ = volume S := by
    rw [show μ = (volume : Measure ℝ).comap Subtype.val from rfl, comap_subtype_coe_apply hS]
    simp
  have hν : ν Set.univ = volume T := by
    rw [show ν = (volume : Measure ℝ).comap Subtype.val from rfl, comap_subtype_coe_apply hT]
    simp
  let : IsFiniteMeasure μ := ⟨by rw [hμ]; exact (measure_mono (inter_subset_right : S ⊆ Ioc u v)).trans_lt (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)⟩
  let : IsFiniteMeasure ν := ⟨by rw [hν]; exact (measure_mono (inter_subset_right : T ⊆ Ioc u v)).trans_lt (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)⟩
  have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  have h := lintegral_rpow_mul_separated_gmc_masses_le hh μ ν hε hr γ
    (fun t => b t.val.toNNReal) (fun t => b t.val.toNNReal)
    (hb.comp measurable_subtype_coe) (hb.comp measurable_subtype_coe)
    (fun t => hx t t.property) (fun t => hy t t.property)
    (fun t s => hxy t t.property s s.property) hq hq2
  have hleft (ω : Ω) : (∫⁻ t : S, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.val.toNNReal) ω) ∂μ) =
      ∫⁻ t in S, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) :=
    lintegral_subtype_comap (μ := (volume : Measure ℝ)) hS
      (fun t => ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))
  have hright (ω : Ω) : (∫⁻ t : T, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.val.toNNReal) ω) ∂ν) =
      ∫⁻ t in T, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) :=
    lintegral_subtype_comap (μ := (volume : Measure ℝ)) hT
      (fun t => ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))
  simp_rw [hleft, hright, hμ, hν] at h
  exact h

/-- Separated path occupation masses over time sets have a uniform fractional cross moment. -/
theorem lintegral_rpow_mul_separated_time_masses_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v : ℝ) (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (hx : ∀ t ∈ A ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hy : ∀ t ∈ B ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hxy : ∀ t ∈ A ∩ Ioc u v, ∀ s ∈ B ∩ Ioc u v,
      r ≤ ‖b t.toNNReal - b s.toNNReal‖) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∫⁻ ω, ((∫⁻ t in A ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) *
      (∫⁻ t in B ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))) ^ (q / 2) ∂P) ≤
      (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        (ENNReal.ofReal (v - u) * ENNReal.ofReal (v - u))) ^ (q / 2) := by
  let S := A ∩ Ioc u v
  let T := B ∩ Ioc u v
  have hS : MeasurableSet S := hA.inter measurableSet_Ioc
  have hT : MeasurableSet T := hB.inter measurableSet_Ioc
  let μ : Measure S := (volume : Measure ℝ).comap Subtype.val
  let ν : Measure T := (volume : Measure ℝ).comap Subtype.val
  have hμ : μ Set.univ = volume S := by
    rw [show μ = (volume : Measure ℝ).comap Subtype.val from rfl, comap_subtype_coe_apply hS]
    simp
  have hν : ν Set.univ = volume T := by
    rw [show ν = (volume : Measure ℝ).comap Subtype.val from rfl, comap_subtype_coe_apply hT]
    simp
  let : IsFiniteMeasure μ := ⟨by rw [hμ]; exact (measure_mono (inter_subset_right : S ⊆ Ioc u v)).trans_lt (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)⟩
  let : IsFiniteMeasure ν := ⟨by rw [hν]; exact (measure_mono (inter_subset_right : T ⊆ Ioc u v)).trans_lt (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)⟩
  have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  have h := lintegral_rpow_mul_separated_gmc_masses_le hh μ ν hε hr γ
    (fun t => b t.val.toNNReal) (fun t => b t.val.toNNReal)
    (hb.comp measurable_subtype_coe) (hb.comp measurable_subtype_coe)
    (fun t => hx t t.property) (fun t => hy t t.property)
    (fun t s => hxy t t.property s s.property) hq hq2
  have hleft (ω : Ω) : (∫⁻ t : S, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.val.toNNReal) ω) ∂μ) =
      ∫⁻ t in S, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) :=
    lintegral_subtype_comap (μ := (volume : Measure ℝ)) hS
      (fun t => ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))
  have hright (ω : Ω) : (∫⁻ t : T, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.val.toNNReal) ω) ∂ν) =
      ∫⁻ t in T, ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) :=
    lintegral_subtype_comap (μ := (volume : Measure ℝ)) hT
      (fun t => ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))
  simp_rw [hleft, hright, hμ, hν] at h
  refine h.trans (ENNReal.rpow_le_rpow ?_ (by positivity))
  gcongr
  · exact (measure_mono (inter_subset_right : S ⊆ Ioc u v)).trans_eq Real.volume_Ioc
  · exact (measure_mono (inter_subset_right : T ⊆ Ioc u v)).trans_eq Real.volume_Ioc
/-- A finite sum of separated time-piece interactions has a uniform fractional moment bound. -/
theorem lintegral_sum_rpow_mul_separated_time_masses_le {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v : ℝ) (F : Finset ι) (A B : ι → Set ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i)) (hB : ∀ i ∈ F, MeasurableSet (B i))
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (hx : ∀ i ∈ F, ∀ t ∈ A i ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hy : ∀ i ∈ F, ∀ t ∈ B i ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hxy : ∀ i ∈ F, ∀ t ∈ A i ∩ Ioc u v, ∀ s ∈ B i ∩ Ioc u v,
      r ≤ ‖b t.toNNReal - b s.toNNReal‖) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∫⁻ ω, ∑ i ∈ F, ((∫⁻ t in A i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) *
      (∫⁻ t in B i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))) ^ (q / 2) ∂P) ≤
      (F.card : ℝ≥0∞) * (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        (ENNReal.ofReal (v - u) * ENNReal.ofReal (v - u))) ^ (q / 2) := by
  classical
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let D : ℂ → Ω → ℝ≥0∞ := LatticeProb.Gauss.gmcDensityENN (fun z ω => H ω ε z) γ ε
  have hD : Measurable (Function.uncurry D) :=
    LatticeProb.Gauss.measurable_uncurry_gmcDensityENN (hHm ε hε) γ ε
  have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  have hmass (S : Set ℝ) : AEMeasurable (fun ω => ∫⁻ t in S,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) P := by
    have hm : Measurable (fun p : Ω × ℝ => D (b p.2.toNNReal) p.1) :=
      hD.comp ((hb.comp measurable_snd).prodMk measurable_fst)
    have heq : (fun ω => ∫⁻ t in S,
        ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) =ᵐ[P]
        (fun ω => ∫⁻ t in S, D (b t.toNNReal) ω) := by
      filter_upwards [hHae] with ω hω
      apply lintegral_congr
      intro t
      simp only [D, LatticeProb.Gauss.gmcDensityENN, LatticeProb.Gauss.gmcDensity, hω]
    exact (hm.lintegral_prod_right' (ν := volume.restrict S)).aemeasurable.congr heq.symm
  have hf : ∀ i ∈ F, AEMeasurable (fun ω => ((∫⁻ t in A i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) *
      (∫⁻ t in B i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))) ^ (q / 2)) P := by
    intro i _
    exact ((hmass (A i ∩ Ioc u v)).mul (hmass (B i ∩ Ioc u v))).pow_const _
  rw [lintegral_finsetSum' F hf]
  calc
    _ ≤ ∑ _i ∈ F, (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        (ENNReal.ofReal (v - u) * ENNReal.ofReal (v - u))) ^ (q / 2) := by
      apply Finset.sum_le_sum
      intro i hi
      exact lintegral_rpow_mul_separated_time_masses_le hh b u v (A i) (B i)
        (hA i hi) (hB i hi) hε hr γ (hx i hi) (hy i hi) (hxy i hi) hq hq2
    _ = _ := by simp

/-- A finite family of separated interactions is bounded by its time-set volumes. -/
theorem lintegral_sum_rpow_mul_separated_time_masses_le_volume {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v : ℝ) (F : Finset ι) (A B : ι → Set ℝ)
    (hA : ∀ i ∈ F, MeasurableSet (A i)) (hB : ∀ i ∈ F, MeasurableSet (B i))
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ : ℝ)
    (hx : ∀ i ∈ F, ∀ t ∈ A i ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hy : ∀ i ∈ F, ∀ t ∈ B i ∩ Ioc u v, ‖b t.toNNReal‖ + ε ≤ 1)
    (hxy : ∀ i ∈ F, ∀ t ∈ A i ∩ Ioc u v, ∀ s ∈ B i ∩ Ioc u v,
      r ≤ ‖b t.toNNReal - b s.toNNReal‖) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∫⁻ ω, ∑ i ∈ F, ((∫⁻ t in A i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) *
      (∫⁻ t in B i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))) ^ (q / 2) ∂P) ≤
      ∑ i ∈ F, (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        (volume (A i ∩ Ioc u v) * volume (B i ∩ Ioc u v))) ^ (q / 2) := by
  classical
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let D : ℂ → Ω → ℝ≥0∞ := LatticeProb.Gauss.gmcDensityENN (fun z ω => H ω ε z) γ ε
  have hD : Measurable (Function.uncurry D) :=
    LatticeProb.Gauss.measurable_uncurry_gmcDensityENN (hHm ε hε) γ ε
  have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  have hmass (S : Set ℝ) : AEMeasurable (fun ω => ∫⁻ t in S,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) P := by
    have hm : Measurable (fun p : Ω × ℝ => D (b p.2.toNNReal) p.1) :=
      hD.comp ((hb.comp measurable_snd).prodMk measurable_fst)
    have heq : (fun ω => ∫⁻ t in S,
        ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) =ᵐ[P]
        (fun ω => ∫⁻ t in S, D (b t.toNNReal) ω) := by
      filter_upwards [hHae] with ω hω
      apply lintegral_congr
      intro t
      simp only [D, LatticeProb.Gauss.gmcDensityENN, LatticeProb.Gauss.gmcDensity, hω]
    exact (hm.lintegral_prod_right' (ν := volume.restrict S)).aemeasurable.congr heq.symm
  have hf : ∀ i ∈ F, AEMeasurable (fun ω => ((∫⁻ t in A i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) *
      (∫⁻ t in B i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))) ^ (q / 2)) P := by
    intro i _
    exact ((hmass (A i ∩ Ioc u v)).mul (hmass (B i ∩ Ioc u v))).pow_const _
  rw [lintegral_finsetSum' F hf]
  apply Finset.sum_le_sum
  intro i hi
  exact lintegral_rpow_mul_separated_time_masses_le_volume hh b u v (A i) (B i)
    (hA i hi) (hB i hi) hε hr γ (hx i hi) (hy i hi) (hxy i hi) hq hq2

private theorem rpow_sum_le_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞)
    {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (∑ i ∈ s, a i) ^ p ≤ ∑ i ∈ s, (a i) ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hp]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact (ENNReal.rpow_add_le_add_rpow _ _ hp.le hp1).trans (add_le_add_right ih _)

/-- A fractional power of a finite mass is bounded by its pair interactions. -/
theorem rpow_sum_le_sum_cross {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞)
    {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∑ i ∈ s, a i) ^ q ≤ ∑ i ∈ s, ∑ j ∈ s, (a i * a j) ^ (q / 2) := by
  have h := rpow_sum_le_sum_rpow s (fun i => ∑ j ∈ s, a i * a j)
    (p := q / 2) (by positivity) (by linarith)
  have hsum : (∑ i ∈ s, (∑ j ∈ s, a i * a j) ^ (q / 2)) ≤
      ∑ i ∈ s, ∑ j ∈ s, (a i * a j) ^ (q / 2) := by
    apply Finset.sum_le_sum
    intro i hi
    exact rpow_sum_le_sum_rpow s (fun j => a i * a j) (by positivity) (by linarith)
  have heq : (∑ i ∈ s, ∑ j ∈ s, a i * a j) = (∑ i ∈ s, a i) ^ (2 : ℕ) := by
    rw [pow_two, Finset.sum_mul_sum]
  rw [heq, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at h
  have h' := h.trans hsum
  convert h' using 1
  congr 1
  ring

/-- A fractional power of a finite mass splits into diagonal and off-diagonal terms. -/
theorem rpow_sum_le_sum_diagonal_add_cross {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ≥0∞)
    {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∑ i ∈ s, a i) ^ q ≤ (∑ i ∈ s, (a i) ^ q) +
      ∑ i ∈ s, ∑ j ∈ s.erase i, (a i * a j) ^ (q / 2) := by
  classical
  refine (rpow_sum_le_sum_cross s a hq hq2).trans_eq ?_
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_erase_add s (fun j => (a i * a j) ^ (q / 2)) hi, add_comm]
  congr 1
  rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  congr 1
  ring


/-- A fractional pair interaction is bounded by the two diagonal powers. -/
theorem rpow_mul_le_add_rpow (a b : ℝ≥0∞) {q : ℝ} (hq : 0 ≤ q) :
    (a * b) ^ (q / 2) ≤ a ^ q + b ^ q := by
  have hmul : a * b ≤ max a b * max a b := mul_le_mul' (le_max_left _ _) (le_max_right _ _)
  have h := ENNReal.rpow_le_rpow hmul (show 0 ≤ q / 2 by positivity)
  have hm : (max a b * max a b) ^ (q / 2) = (max a b) ^ q := by
    rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1
    ring
  rw [hm] at h
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab] at h
    exact h.trans (le_add_left le_rfl)
  · rw [max_eq_left hba] at h
    exact h.trans (le_add_right le_rfl)

/-- A bounded-degree symmetric relation controls its total fractional interaction. -/
theorem sum_rpow_mul_le_degree_mul_sum_rpow {ι : Type*} (s : Finset ι) (a : ι → ℝ≥0∞) (R : ι → ι → Prop)
    [DecidableRel R] (hsym : ∀ ⦃i j⦄, R i j → R j i) (D : ℕ)
    (hdegree : ∀ i ∈ s, (s.filter (R i)).card ≤ D) {q : ℝ} (hq : 0 ≤ q) :
    (∑ i ∈ s, ∑ j ∈ s.filter (R i), (a i * a j) ^ (q / 2)) ≤
      (2 * (D : ℝ≥0∞)) * ∑ i ∈ s, a i ^ q := by
  classical
  have hsum : (∑ i ∈ s, ∑ j ∈ s.filter (R i), a j ^ q) =
      ∑ i ∈ s, ∑ j ∈ s.filter (R i), a i ^ q := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : R i j
    · simp [h, hsym h]
    · have hn : ¬ R j i := fun hji => h (hsym hji)
      simp [h, hn]
  have hrow : (∑ i ∈ s, ∑ j ∈ s.filter (R i), a i ^ q) ≤
      (D : ℝ≥0∞) * ∑ i ∈ s, a i ^ q := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Finset.sum_const, nsmul_eq_mul]
    gcongr
    exact_mod_cast hdegree i hi
  calc
    _ ≤ ∑ i ∈ s, ∑ j ∈ s.filter (R i), (a i ^ q + a j ^ q) := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => rpow_mul_le_add_rpow _ _ hq
    _ = (∑ i ∈ s, ∑ j ∈ s.filter (R i), a i ^ q) +
        (∑ i ∈ s, ∑ j ∈ s.filter (R i), a j ^ q) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ _ := by rw [hsum]; calc
      _ ≤ (D : ℝ≥0∞) * (∑ i ∈ s, a i ^ q) +
          (D : ℝ≥0∞) * (∑ i ∈ s, a i ^ q) := add_le_add hrow hrow
      _ = _ := by simp only [two_mul]; rw [add_mul]

/-- Two integer square indices are adjacent when both coordinate differences are at most one. -/
def squareGridAdjacent (i j : ℤ × ℤ) : Prop :=
  |i.1 - j.1| ≤ 1 ∧ |i.2 - j.2| ≤ 1

instance (i j : ℤ × ℤ) : Decidable (squareGridAdjacent i j) := by
  unfold squareGridAdjacent
  infer_instance

/-- Square-grid adjacency is symmetric. -/
theorem squareGridAdjacent_symm {i j : ℤ × ℤ} (h : squareGridAdjacent i j) :
    squareGridAdjacent j i := by
  constructor <;> simp only [squareGridAdjacent] at *
  · simpa [abs_sub_comm] using h.1
  · simpa [abs_sub_comm] using h.2

/-- A square has at most nine adjacent squares in any finite grid. -/
theorem squareGridAdjacent_card_le (s : Finset (ℤ × ℤ)) (i : ℤ × ℤ) :
    (s.filter (squareGridAdjacent i)).card ≤ 9 := by
  let t : Finset (ℤ × ℤ) := (Finset.Icc (i.1 - 1) (i.1 + 1)).product
    (Finset.Icc (i.2 - 1) (i.2 + 1))
  have hsub : s.filter (squareGridAdjacent i) ⊆ t := by
    intro j hj
    have h := (Finset.mem_filter.mp hj).2
    simp only [squareGridAdjacent, abs_le] at h
    change j ∈ (Finset.Icc (i.1 - 1) (i.1 + 1)).product
      (Finset.Icc (i.2 - 1) (i.2 + 1))
    simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc]
    omega
  calc
    _ ≤ t.card := Finset.card_le_card hsub
    _ = 9 := by
      simp only [t, Finset.product_eq_sprod, Finset.card_product, Int.card_Icc]
      have h1 : i.1 + 1 + 1 - (i.1 - 1) = (3 : ℤ) := by omega
      have h2 : i.2 + 1 + 1 - (i.2 - 1) = (3 : ℤ) := by omega
      rw [h1, h2]
      decide

/-- Adjacent square interactions are controlled by the diagonal powers. -/
theorem sum_rpow_mul_squareGridAdjacent_le (s : Finset (ℤ × ℤ))
    (a : ℤ × ℤ → ℝ≥0∞) {q : ℝ} (hq : 0 ≤ q) :
    (∑ i ∈ s, ∑ j ∈ s.filter (squareGridAdjacent i), (a i * a j) ^ (q / 2)) ≤
      18 * ∑ i ∈ s, a i ^ q := by
  convert sum_rpow_mul_le_degree_mul_sum_rpow s a squareGridAdjacent
    (fun {_ _} h => squareGridAdjacent_symm h) 9
    (fun i _ => squareGridAdjacent_card_le s i) hq using 1; norm_num


private theorem square_coordinate_separation {r : ℝ} (hr : 0 < r) {a b : ℤ}
    (hab : a + 2 ≤ b ∨ b + 2 ≤ a) {u v : ℝ}
    (hu : (a : ℝ) * r ≤ u ∧ u < ((a : ℝ) + 1) * r)
    (hv : (b : ℝ) * r ≤ v ∧ v < ((b : ℝ) + 1) * r) : r ≤ |u - v| := by
  rcases hab with hab | hab
  · have h : (a : ℝ) + 2 ≤ b := by exact_mod_cast hab
    have hm := mul_le_mul_of_nonneg_right h hr.le
    have hvu : r ≤ v - u := by nlinarith [hu.2, hv.1]
    exact hvu.trans (by rw [abs_sub_comm]; exact le_abs_self _)
  · have h : (b : ℝ) + 2 ≤ a := by exact_mod_cast hab
    have hm := mul_le_mul_of_nonneg_right h hr.le
    have huv : r ≤ u - v := by nlinarith [hv.2, hu.1]
    exact huv.trans (le_abs_self _)

/-- Points in nonadjacent half-open squares are separated by the side length. -/
theorem le_norm_sub_of_not_squareGridAdjacent {r : ℝ} (hr : 0 < r)
    {i j : ℤ × ℤ} (hij : ¬ squareGridAdjacent i j) {x y : ℂ}
    (hx : x ∈ LatticeProb.dyadicSquare r i) (hy : y ∈ LatticeProb.dyadicSquare r j) :
    r ≤ ‖x - y‖ := by
  have hd : (i.1 + 2 ≤ j.1 ∨ j.1 + 2 ≤ i.1) ∨
      (i.2 + 2 ≤ j.2 ∨ j.2 + 2 ≤ i.2) := by
    simp only [squareGridAdjacent, abs_le, not_and_or, not_le] at hij
    omega
  rw [LatticeProb.mem_dyadicSquare] at hx hy
  rcases hd with h | h
  · exact (square_coordinate_separation hr h hx.1 hy.1).trans
      (by simpa using Complex.abs_re_le_norm (x - y))
  · exact (square_coordinate_separation hr h hx.2 hy.2).trans
      (by simpa using Complex.abs_im_le_norm (x - y))

/-- Times at which a path visits one square inside the annulus. -/
def annularSquareTimeSet (b : ContinuousPath ℂ) (δ r : ℝ) (i : ℤ × ℤ) : Set ℝ :=
  {t | b t.toNNReal ∈ LatticeProb.dyadicSquare r i ∧
    δ ≤ ‖b t.toNNReal‖ ∧ ‖b t.toNNReal‖ ≤ 1 / 2}

/-- The time set of a square inside the annulus is measurable. -/
theorem measurableSet_annularSquareTimeSet (b : ContinuousPath ℂ) (δ r : ℝ) (i : ℤ × ℤ) :
    MeasurableSet (annularSquareTimeSet b δ r i) := by
  have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  exact ((LatticeProb.measurableSet_dyadicSquare r i).preimage hb).inter
    ((measurableSet_le measurable_const hb.norm).inter (measurableSet_le hb.norm measurable_const))

/-- Nonadjacent annular square occupation masses have a uniform cross-moment bound. -/
theorem lintegral_rpow_mul_annularSquareTime_masses_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v δ : ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hr : 0 < r) (γ : ℝ)
    {i j : ℤ × ℤ} (hij : ¬ squareGridAdjacent i j) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∫⁻ ω, ((∫⁻ t in annularSquareTimeSet b δ r i ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) *
      (∫⁻ t in annularSquareTimeSet b δ r j ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω))) ^ (q / 2) ∂P) ≤
      (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
        (ENNReal.ofReal (v - u) * ENNReal.ofReal (v - u))) ^ (q / 2) := by
  apply lintegral_rpow_mul_separated_time_masses_le hh b u v _ _
    (measurableSet_annularSquareTimeSet b δ r i) (measurableSet_annularSquareTimeSet b δ r j)
    hε hr γ
  · intro t ht
    exact add_le_of_le_sub_left (by linarith [ht.1.2.2])
  · intro t ht
    exact add_le_of_le_sub_left (by linarith [ht.1.2.2])
  · intro t ht s hs
    exact le_norm_sub_of_not_squareGridAdjacent hr hij ht.1.1 hs.1.1
  · exact hq
  · exact hq2

/-- An annular time integral is the sum over the finite square cover. -/
theorem lintegral_annular_time_eq_sum_square (b : ContinuousPath ℂ) (δ u v : ℝ)
    {r : ℝ} (hr : 0 < r) (f : ℝ → ℝ≥0∞) :
    (∫⁻ t in {t | δ ≤ ‖b t.toNNReal‖ ∧ ‖b t.toNNReal‖ ≤ 1 / 2} ∩ Ioc u v, f t) =
      ∑ i ∈ LatticeProb.squareIndex r, ∫⁻ t in annularSquareTimeSet b δ r i ∩ Ioc u v, f t := by
  have hu : (⋃ i ∈ LatticeProb.squareIndex r, annularSquareTimeSet b δ r i ∩ Ioc u v) =
      {t | δ ≤ ‖b t.toNNReal‖ ∧ ‖b t.toNNReal‖ ≤ 1 / 2} ∩ Ioc u v := by
    ext t
    simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq, annularSquareTimeSet]
    constructor
    · rintro ⟨i, hi, ⟨⟨hmem, ha, hb⟩, ht⟩⟩
      exact ⟨⟨ha, hb⟩, ht⟩
    · rintro ⟨⟨ha, hb⟩, ht⟩
      have hball : b t.toNNReal ∈ Metric.closedBall (0 : ℂ) (1 / 2) := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hb
      have hcover := LatticeProb.closedBall_subset_iUnion_dyadicSquare hr hball
      simp only [mem_iUnion] at hcover
      obtain ⟨i, hi, hmem⟩ := hcover
      exact ⟨i, hi, ⟨⟨hmem, ha, hb⟩, ht⟩⟩
  rw [← hu]
  apply lintegral_biUnion_finset
  · intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro t hti htj
    exact Set.disjoint_left.mp (LatticeProb.disjoint_dyadicSquare hr hij) hti.1.1 htj.1.1
  · intro i hi
    exact (measurableSet_annularSquareTimeSet b δ r i).inter measurableSet_Ioc

/-- The fractional power of a grid mass separates adjacent and distant interactions. -/
theorem rpow_sum_le_squareGridAdjacent_add_far (s : Finset (ℤ × ℤ))
    (a : ℤ × ℤ → ℝ≥0∞) {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    (∑ i ∈ s, a i) ^ q ≤ 18 * (∑ i ∈ s, a i ^ q) +
      ∑ i ∈ s, ∑ j ∈ s.filter (fun j => ¬ squareGridAdjacent i j),
        (a i * a j) ^ (q / 2) := by
  classical
  have hs : (∑ i ∈ s, ∑ j ∈ s, (a i * a j) ^ (q / 2)) =
      (∑ i ∈ s, ∑ j ∈ s.filter (squareGridAdjacent i), (a i * a j) ^ (q / 2)) +
      (∑ i ∈ s, ∑ j ∈ s.filter (fun j => ¬ squareGridAdjacent i j),
        (a i * a j) ^ (q / 2)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.sum_filter_add_sum_filter_not s (squareGridAdjacent i) _).symm
  exact (rpow_sum_le_sum_cross s a hq hq2).trans (by
    rw [hs]
    exact add_le_add (sum_rpow_mul_squareGridAdjacent_le s a hq.le) le_rfl)

/-- The field moment of an annular mass is bounded by square moments and separated interactions. -/
theorem lintegral_annular_mass_rpow_le_square_moments_add_far {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v δ : ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hr : 0 < r) (γ : ℝ)
    {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    let S := LatticeProb.squareIndex r
    let T := fun i => annularSquareTimeSet b δ r i ∩ Ioc u v
    let M := fun i ω => ∫⁻ t in T i,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)
    (∫⁻ ω, (∫⁻ t in {t | δ ≤ ‖b t.toNNReal‖ ∧ ‖b t.toNNReal‖ ≤ 1 / 2} ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) ^ q ∂P) ≤
      18 * (∑ i ∈ S, ∫⁻ ω, (M i ω) ^ q ∂P) +
      ∑ i ∈ S, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
        (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (volume (T i) * volume (T j))) ^ (q / 2) := by
  classical
  dsimp only
  let S := LatticeProb.squareIndex r
  let T := fun i => annularSquareTimeSet b δ r i ∩ Ioc u v
  let M := fun i ω => ∫⁻ t in T i,
    ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)
  change (∫⁻ ω, (∫⁻ t in {t | δ ≤ ‖b t.toNNReal‖ ∧ ‖b t.toNNReal‖ ≤ 1 / 2} ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) ^ q ∂P) ≤
      18 * (∑ i ∈ S, ∫⁻ ω, (M i ω) ^ q ∂P) +
      ∑ i ∈ S, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
        (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (volume (T i) * volume (T j))) ^ (q / 2)
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let D : ℂ → Ω → ℝ≥0∞ := LatticeProb.Gauss.gmcDensityENN (fun z ω => H ω ε z) γ ε
  have hD : Measurable (Function.uncurry D) :=
    LatticeProb.Gauss.measurable_uncurry_gmcDensityENN (hHm ε hε) γ ε
  have hb : Measurable (fun t : ℝ => b t.toNNReal) := by fun_prop
  have hmass (i : ℤ × ℤ) : AEMeasurable (M i) P := by
    have hm : Measurable (fun p : Ω × ℝ => D (b p.2.toNNReal) p.1) :=
      hD.comp ((hb.comp measurable_snd).prodMk measurable_fst)
    have heq : M i =ᵐ[P] (fun ω => ∫⁻ t in T i, D (b t.toNNReal) ω) := by
      filter_upwards [hHae] with ω hω
      apply lintegral_congr
      intro t
      simp only [D, LatticeProb.Gauss.gmcDensityENN, LatticeProb.Gauss.gmcDensity, hω]
    exact (hm.lintegral_prod_right' (ν := volume.restrict (T i))).aemeasurable.congr heq.symm
  have hdiag : AEMeasurable (fun ω => ∑ i ∈ S, (M i ω) ^ q) P := by
    convert Finset.aemeasurable_sum S (fun i _ => (hmass i).pow_const q) using 1
    ext ω
    simp only [Finset.sum_apply]
  have hfar (i j : ℤ × ℤ) (hij : ¬ squareGridAdjacent i j) :
      (∫⁻ ω, (M i ω * M j ω) ^ (q / 2) ∂P) ≤
        (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (volume (T i) * volume (T j))) ^ (q / 2) := by
    apply lintegral_rpow_mul_separated_time_masses_le_volume hh b u v _ _
      (measurableSet_annularSquareTimeSet b δ r i) (measurableSet_annularSquareTimeSet b δ r j)
      hε hr γ
    · intro t ht
      exact add_le_of_le_sub_left (by linarith [ht.1.2.2])
    · intro t ht
      exact add_le_of_le_sub_left (by linarith [ht.1.2.2])
    · intro t ht s hs
      exact le_norm_sub_of_not_squareGridAdjacent hr hij ht.1.1 hs.1.1
    · exact hq
    · exact hq2
  calc
    _ ≤ ∫⁻ ω, 18 * (∑ i ∈ S, (M i ω) ^ q) +
        ∑ i ∈ S, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
          (M i ω * M j ω) ^ (q / 2) ∂P := by
      apply lintegral_mono
      intro ω
      dsimp only
      rw [lintegral_annular_time_eq_sum_square b δ u v hr]
      exact rpow_sum_le_squareGridAdjacent_add_far S (fun i => M i ω) hq hq2
    _ = 18 * (∑ i ∈ S, ∫⁻ ω, (M i ω) ^ q ∂P) +
        ∑ i ∈ S, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
          ∫⁻ ω, (M i ω * M j ω) ^ (q / 2) ∂P := by
      have hrow (i : ℤ × ℤ) :
          (∫⁻ ω, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
            (M i ω * M j ω) ^ (q / 2) ∂P) =
          ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
            ∫⁻ ω, (M i ω * M j ω) ^ (q / 2) ∂P := by
        exact lintegral_finsetSum' _ (fun j _ => ((hmass i).mul (hmass j)).pow_const _)
      have houter :
          (∫⁻ ω, ∑ i ∈ S, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
            (M i ω * M j ω) ^ (q / 2) ∂P) =
          ∑ i ∈ S, ∫⁻ ω, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
            (M i ω * M j ω) ^ (q / 2) ∂P := by
        apply lintegral_finsetSum'
        intro i hi
        convert Finset.aemeasurable_sum (S.filter (fun j => ¬ squareGridAdjacent i j))
          (fun j _ => ((hmass i).mul (hmass j)).pow_const (q / 2)) using 1
        ext ω
        simp only [Finset.sum_apply, Pi.mul_apply]
      rw [lintegral_add_left' (hdiag.const_mul 18), lintegral_const_mul'' _ hdiag, houter]
      simp_rw [hrow]
      rw [lintegral_finsetSum' S (fun i _ => (hmass i).pow_const _)]
    _ ≤ _ := by
      gcongr with i hi j hj
      exact hfar i j (Finset.mem_filter.mp hj).2

/-- The separated contribution has a path-independent time-cell bound. -/
theorem lintegral_annular_mass_rpow_le_square_moments_add_cell {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v δ : ℝ) {ε r : ℝ}
    (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (hr : 0 < r) (γ : ℝ)
    {q : ℝ} (hq : 0 < q) (hq2 : q ≤ 2) :
    let S := LatticeProb.squareIndex r
    let T := fun i => annularSquareTimeSet b δ r i ∩ Ioc u v
    let M := fun i ω => ∫⁻ t in T i,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)
    (∫⁻ ω, (∫⁻ t in {t | δ ≤ ‖b t.toNNReal‖ ∧ ‖b t.toNNReal‖ ≤ 1 / 2} ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)) ^ q ∂P) ≤
      18 * (∑ i ∈ S, ∫⁻ ω, (M i ω) ^ q ∂P) +
      (S.card : ℝ≥0∞) * ((S.card : ℝ≥0∞) *
        (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
          (ENNReal.ofReal (v - u) * ENNReal.ofReal (v - u))) ^ (q / 2)) := by
  classical
  dsimp only
  let S := LatticeProb.squareIndex r
  let T := fun i => annularSquareTimeSet b δ r i ∩ Ioc u v
  let B := (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) *
    (ENNReal.ofReal (v - u) * ENNReal.ofReal (v - u))) ^ (q / 2)
  have hvol (i : ℤ × ℤ) : volume (T i) ≤ ENNReal.ofReal (v - u) :=
    (measure_mono (inter_subset_right : T i ⊆ Ioc u v)).trans_eq Real.volume_Ioc
  have hterm (i j : ℤ × ℤ) :
      (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (volume (T i) * volume (T j))) ^ (q / 2) ≤ B := by
    apply ENNReal.rpow_le_rpow _ (by positivity)
    exact mul_le_mul' le_rfl (mul_le_mul' (hvol i) (hvol j))
  have hrow (i : ℤ × ℤ) :
      (∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
        (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (volume (T i) * volume (T j))) ^ (q / 2)) ≤
        (S.card : ℝ≥0∞) * B := by
    calc
      _ ≤ ∑ _j ∈ S.filter (fun j => ¬ squareGridAdjacent i j), B :=
        Finset.sum_le_sum fun j _ => hterm i j
      _ = ((S.filter (fun j => ¬ squareGridAdjacent i j)).card : ℝ≥0∞) * B := by simp
      _ ≤ (S.card : ℝ≥0∞) * B := by
        gcongr
        exact Finset.filter_subset _ _
  have hsum :
      (∑ i ∈ S, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
        (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (volume (T i) * volume (T j))) ^ (q / 2)) ≤
        (S.card : ℝ≥0∞) * ((S.card : ℝ≥0∞) * B) := by
    calc
      _ ≤ ∑ _i ∈ S, (S.card : ℝ≥0∞) * B := Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by simp
  exact (lintegral_annular_mass_rpow_le_square_moments_add_far hh b u v δ hε hε2 hr γ hq hq2).trans
    (add_le_add le_rfl hsum)

/-- A grid square maps into the reference square under rescaling about its centre. -/
theorem dyadicSquare_rescaled_mem_lqgSquare {r : ℝ} (hr : 0 < r)
    {i : ℤ × ℤ} {z : ℂ} (hz : z ∈ LatticeProb.dyadicSquare r i) :
    (z - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ) ∈ LatticeProb.LQG.lqgSquare := by
  rw [LatticeProb.mem_dyadicSquare] at hz
  rcases hz with ⟨⟨h1, h2⟩, h3, h4⟩
  simp only [LatticeProb.LQG.lqgSquare, Set.mem_ofPred_eq, Complex.div_ofReal_re,
    Complex.div_ofReal_im, Complex.sub_re, Complex.sub_im,
    LatticeProb.dyadicSquareCentre]
  constructor <;> rw [abs_le] <;> constructor <;>
    (first | apply (le_div_iff₀ (by positivity : 0 < 4 * r)).2 | apply (div_le_iff₀ (by positivity : 0 < 4 * r)).2) <;> nlinarith

/-- The comparison circle around each square centre lies in the unit disc. -/
theorem norm_dyadicSquareCentre_add_four_mul_le_one {r : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) :
    ‖LatticeProb.dyadicSquareCentre r i‖ + 4 * r ≤ 1 := by
  have h := LatticeProb.norm_dyadicSquareCentre_lt hr hi
  linarith

/-- Circle-average covariance scales around every centre in the square cover. -/
theorem covariance_circle_annularSquare_rescaled
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) {w w' : ℂ}
    (hw : w ∈ LatticeProb.LQG.lqgSquare) (hw' : w' ∈ LatticeProb.LQG.lqgSquare) :
    cov[fun ω => hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * w + LatticeProb.dyadicSquareCentre r i),
        fun ω => hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * w' + LatticeProb.dyadicSquareCentre r i); P] =
      -Real.log (4 * r) + cov[fun ω => hcirc ω δ w, fun ω => hcirc ω δ w'; P] := by
  apply hh.covariance_circle_rescaled (by positivity) hδ (norm_dyadicSquareCentre_add_four_mul_le_one hr hr10 hi)
  · have h := LatticeProb.LQG.lqgSquare_subset_closedBall hw
    simp only [Metric.mem_closedBall, dist_zero_right] at h
    linarith
  · have h := LatticeProb.LQG.lqgSquare_subset_closedBall hw'
    simp only [Metric.mem_closedBall, dist_zero_right] at h
    linarith


/-- Circle-average covariance for two points in a square of the cover. -/
theorem covariance_circle_annularSquare
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) {z z' : ℂ}
    (hz : z ∈ LatticeProb.dyadicSquare r i) (hz' : z' ∈ LatticeProb.dyadicSquare r i) :
    cov[fun ω => hcirc ω (4 * r * δ) z, fun ω => hcirc ω (4 * r * δ) z'; P] =
      -Real.log (4 * r) + cov[
        fun ω => hcirc ω δ ((z - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)),
        fun ω => hcirc ω δ ((z' - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)); P] := by
  have h := covariance_circle_annularSquare_rescaled hh hr hr10 hδ hδ2 hi
    (dyadicSquare_rescaled_mem_lqgSquare hr hz) (dyadicSquare_rescaled_mem_lqgSquare hr hz')
  have hR : (((4 * r : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (show 4 * r ≠ 0 by positivity)
  simpa only [mul_div_cancel₀ _ hR, sub_add_cancel] using h

/-- Finite atomic masses in any grid square admit a rescaled Gaussian comparison. -/
theorem integral_rpow_annularSquare_atoms_le {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    [Nonempty ι] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ) (pt : ι → ℂ)
    (hpt : ∀ j, pt j ∈ LatticeProb.LQG.lqgSquare)
    (a : ι → ℝ) (ha : ∀ j, 0 < a j) {q : ℝ} (hq : 1 ≤ q) :
    let X := fun ω j => γ * hcirc ω (4 * r * δ)
      (((4 * r : ℝ) : ℂ) * pt j + LatticeProb.dyadicSquareCentre r i)
    let Y := fun ω j => γ * hcirc ω δ (pt j)
    (∫ ω, (∑ j, a j * Real.exp (X ω j - variance (fun ω => X ω j) P / 2)) ^ q ∂P) ≤
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) *
        ∫ ω, (∑ j, a j * Real.exp (Y ω j - variance (fun ω => Y ω j) P / 2)) ^ q ∂P := by
  let X := fun ω j => γ * hcirc ω (4 * r * δ)
    (((4 * r : ℝ) : ℂ) * pt j + LatticeProb.dyadicSquareCentre r i)
  let Y := fun ω j => γ * hcirc ω δ (pt j)
  have hP := hh.isProbabilityMeasure
  have hR : 0 < 4 * r := by positivity
  have hR1 : 4 * r ≤ 1 := by linarith
  have hε : 0 < 4 * r * δ := mul_pos hR hδ
  have hX : HasGaussianLaw X P := by
    have h := LatticeProb.hasGaussianLaw_vector_of_isGaussianProcess hh.isGaussianProcess
      (fun j : ι => (⟨.circle (4 * r * δ)
        (((4 * r : ℝ) : ℂ) * pt j + LatticeProb.dyadicSquareCentre r i), hε⟩ :
          LatticeProb.Gauss.GFFObservable.Admissible))
    have hv := h.fun_smul γ
    convert hv using 2 with ω
    funext j
    simp [X, LatticeProb.Gauss.GFFObservable.eval]
  have hY : HasGaussianLaw Y P := by
    have h := LatticeProb.hasGaussianLaw_vector_of_isGaussianProcess hh.isGaussianProcess
      (fun j : ι => (⟨.circle δ (pt j), hδ⟩ : LatticeProb.Gauss.GFFObservable.Admissible))
    have hv := h.fun_smul γ
    convert hv using 2 with ω
    funext j
    simp [Y, LatticeProb.Gauss.GFFObservable.eval]
  have hXm (j : ι) : ∫ ω, X ω j ∂P = 0 := by
    have hm := hh.integral_eq_zero (.circle (4 * r * δ)
      (((4 * r : ℝ) : ℂ) * pt j + LatticeProb.dyadicSquareCentre r i)) hε
    change (∫ ω, hcirc ω (4 * r * δ) _ ∂P) = 0 at hm
    simp only [X, integral_const_mul, hm, mul_zero]
  have hYm (j : ι) : ∫ ω, Y ω j ∂P = 0 := by
    have hm := hh.integral_eq_zero (.circle δ (pt j)) hδ
    change (∫ ω, hcirc ω δ (pt j) ∂P) = 0 at hm
    simp only [Y, integral_const_mul, hm, mul_zero]
  let C : ℝ≥0 := ⟨-γ ^ 2 * Real.log (4 * r), mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (sq_nonneg γ))
    (Real.log_nonpos hR.le hR1)⟩
  have hcov (j k : ι) : cov[fun ω => X ω j, fun ω => X ω k; P] ≤
      cov[fun ω => Y ω j, fun ω => Y ω k; P] + (C : ℝ) := by
    dsimp only [X, Y, C, NNReal.coe_mk]
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_const_mul_left, covariance_const_mul_right,
      covariance_circle_annularSquare_rescaled hh hr hr10 hδ hδ2 hi (hpt j) (hpt k)]
    change γ * (γ * (-Real.log (4 * r) +
      cov[fun ω => hcirc ω δ (pt j), fun ω => hcirc ω δ (pt k); P])) ≤
      γ * (γ * cov[fun ω => hcirc ω δ (pt j), fun ω => hcirc ω δ (pt k); P]) +
        (-γ ^ 2 * Real.log (4 * r))
    ring_nf
    exact le_rfl
  exact LatticeProb.Kahane.kahane_rpow_le_add_const (Or.inr hq) ha hX hY hXm hYm C hcov


/-- The square comparison permits zero weights and empty atomic families. -/
theorem integral_rpow_annularSquare_atoms_le_nonneg {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ) (pt : ι → ℂ)
    (hpt : ∀ j, pt j ∈ LatticeProb.LQG.lqgSquare)
    (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) {q : ℝ} (hq : 1 ≤ q) :
    let X := fun ω j => γ * hcirc ω (4 * r * δ)
      (((4 * r : ℝ) : ℂ) * pt j + LatticeProb.dyadicSquareCentre r i)
    let Y := fun ω j => γ * hcirc ω δ (pt j)
    (∫ ω, (∑ j, a j * Real.exp (X ω j - variance (fun ω => X ω j) P / 2)) ^ q ∂P) ≤
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) *
        ∫ ω, (∑ j, a j * Real.exp (Y ω j - variance (fun ω => Y ω j) P / 2)) ^ q ∂P := by
  classical
  dsimp only
  by_cases hpos : ∃ j, 0 < a j
  · let : Nonempty {j : ι // 0 < a j} := ⟨⟨hpos.choose, hpos.choose_spec⟩⟩
    have hsum (f : ι → ℝ) : (∑ j : {j : ι // 0 < a j}, a j * f j) = ∑ j, a j * f j := by
      rw [← Finset.sum_subtype (p := fun j => 0 < a j)
        (Finset.univ.filter (fun j => 0 < a j)) (by simp) (fun j => a j * f j)]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro j _ hj
      have hz : a j = 0 := le_antisymm (le_of_not_gt (by simpa using hj)) (ha j)
      simp [hz]
    have h := integral_rpow_annularSquare_atoms_le hh hr hr10 hδ hδ2 hi γ
      (fun j : {j : ι // 0 < a j} => pt j) (fun j => hpt j) (fun j => a j)
      (fun j => j.property) hq
    dsimp only at h
    have hx (ω : Ω) := hsum (fun j => Real.exp
      (γ * hcirc ω (4 * r * δ)
        (((4 * r : ℝ) : ℂ) * pt j + LatticeProb.dyadicSquareCentre r i) -
        variance (fun ω => γ * hcirc ω (4 * r * δ)
          (((4 * r : ℝ) : ℂ) * pt j + LatticeProb.dyadicSquareCentre r i)) P / 2))
    have hy (ω : Ω) := hsum (fun j => Real.exp
      (γ * hcirc ω δ (pt j) - variance (fun ω => γ * hcirc ω δ (pt j)) P / 2))
    simp_rw [hx, hy] at h
    exact h
  · have hz : ∀ j, a j = 0 := fun j => le_antisymm
      (le_of_not_gt (fun hj => hpos ⟨j, hj⟩)) (ha j)
    simp [hz, Real.zero_rpow (by linarith : q ≠ 0)]


/-- A weighted finite family of normalized Gaussian exponentials has a moment
bounded by the corresponding one-point moment. -/
theorem integral_rpow_sum_exp_gaussian_le_of_sum_eq_one
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    (X : ι → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (V : ℝ)
    (hvar : ∀ i, variance (X i) P = V)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (ha1 : ∑ i, a i = 1)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ ω, (∑ i, a i * Real.exp (X i ω - V / 2)) ^ p ∂P) ≤
      Real.exp ((p ^ 2 - p) * V / 2) := by
  classical
  let F : Ω → ι → ℝ := fun ω i => Real.exp (X i ω - V / 2)
  have hI (i : ι) : Integrable (fun ω => F ω i ^ p) P := by
    have hL : HasLaw (X i) (gaussianReal (∫ ω, X i ω ∂P) (variance (X i) P).toNNReal) P :=
      ⟨(hX i).aemeasurable, (hX i).map_eq_gaussianReal⟩
    have hi := hL.integrable_comp (f := fun y : ℝ => Real.exp (p * y))
      (integrable_exp_mul_gaussianReal p)
    have heq : (fun ω => F ω i ^ p) =
        (fun ω => Real.exp (-(p * V / 2)) * Real.exp (p * X i ω)) := by
      funext ω
      dsimp [F]
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    rw [heq]
    exact hi.const_mul _
  have hsum : Integrable (fun ω => ∑ i, a i * F ω i ^ p) P :=
    integrable_finsetSum _ (fun i _ => (hI i).const_mul (a i))
  have hle (ω) : (∑ i, a i * F ω i) ^ p ≤ ∑ i, a i * F ω i ^ p :=
    Real.rpow_arith_mean_le_arith_mean_rpow Finset.univ a (F ω)
      (fun i _ => ha i) ha1 (fun i _ => (Real.exp_pos _).le) hp
  have hint : Integrable (fun ω => (∑ i, a i * F ω i) ^ p) P := by
    simpa only [F] using integrable_rpow_sum_exp_gaussian X hX a (fun _ => V / 2) ha (by linarith : 0 < p)
  calc
    _ ≤ ∫ ω, ∑ i, a i * F ω i ^ p ∂P := integral_mono hint hsum hle
    _ = ∑ i, a i * ∫ ω, F ω i ^ p ∂P := by
      rw [integral_finsetSum _ (fun i _ => (hI i).const_mul _)]
      simp only [integral_const_mul]
    _ = _ := by
      have hmoment (i : ι) : (∫ ω, F ω i ^ p ∂P) =
          Real.exp ((p ^ 2 - p) * V / 2) := by
        have hV : 0 ≤ V := (hvar i) ▸ variance_nonneg (X i) P
        have hL : HasLaw (X i) (gaussianReal 0 V.toNNReal) P :=
          ⟨(hX i).aemeasurable, by rw [(hX i).map_eq_gaussianReal, hmean i, hvar i]⟩
        have hm := mgf_gaussianReal hL p
        simp only [mgf, zero_mul, zero_add, Real.coe_toNNReal V hV] at hm
        simp_rw [F, ← Real.exp_mul, show ∀ ω, Real.exp ((X i ω - V / 2) * p) =
            Real.exp (-(p * V / 2)) * Real.exp (p * X i ω) by
          intro ω
          rw [← Real.exp_add]
          congr 1
          ring]
        rw [integral_const_mul, hm, ← Real.exp_add]
        congr 1
        ring
      simp_rw [hmoment, ← Finset.sum_mul, ha1, one_mul]

/-- A finite atomic Gaussian mass has a moment bounded by its total weight. -/
theorem integral_rpow_sum_exp_gaussian_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    (X : ι → Ω → ℝ) (hX : ∀ i, HasGaussianLaw (X i) P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (V : ℝ)
    (hvar : ∀ i, variance (X i) P = V)
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) {p : ℝ} (hp : 1 ≤ p) :
    (∫ ω, (∑ i, a i * Real.exp (X i ω - V / 2)) ^ p ∂P) ≤
      (∑ i, a i) ^ p * Real.exp ((p ^ 2 - p) * V / 2) := by
  classical
  let M := ∑ i, a i
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => ha i)
  rcases hM.eq_or_lt with hzero | hpos
  · have ha0 (i : ι) : a i = 0 := by
      have hi : a i ≤ M := Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
      exact le_antisymm (by simpa [← hzero] using hi) (ha i)
    simp [ha0, Real.zero_rpow (by linarith : p ≠ 0)]
  · let b : ι → ℝ := fun i => a i / M
    have hb (i : ι) : 0 ≤ b i := div_nonneg (ha i) hpos.le
    have hb1 : ∑ i, b i = 1 := by
      simp only [b, ← Finset.sum_div]
      exact div_self (ne_of_gt hpos)
    have hn := integral_rpow_sum_exp_gaussian_le_of_sum_eq_one X hX hmean V hvar b hb hb1 hp
    have hscale (ω : Ω) :
        (∑ i, a i * Real.exp (X i ω - V / 2)) ^ p =
        M ^ p * (∑ i, b i * Real.exp (X i ω - V / 2)) ^ p := by
      have heq : (∑ i, a i * Real.exp (X i ω - V / 2)) =
          M * (∑ i, b i * Real.exp (X i ω - V / 2)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        dsimp [b]
        field_simp
      rw [heq, Real.mul_rpow hpos.le (Finset.sum_nonneg (fun i _ =>
        mul_nonneg (hb i) (Real.exp_pos _).le))]
    simp_rw [hscale, integral_const_mul]
    exact mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hM _)

/-- At a fixed smoothing scale, moments of finite atomic circle-average masses
are controlled by their total weight. -/
theorem integral_rpow_sum_circle_atoms_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (pt : ι → ℂ)
    (hpt : ∀ i, ‖pt i‖ + ε ≤ 1) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫ ω, (∑ i, a i * Real.exp (γ * hcirc ω ε (pt i) -
      (γ ^ 2 * (-Real.log ε)) / 2)) ^ p ∂P) ≤
    (∑ i, a i) ^ p * Real.exp ((p ^ 2 - p) * (γ ^ 2 * (-Real.log ε)) / 2) := by
  let X : ι → Ω → ℝ := fun i ω => γ * hcirc ω ε (pt i)
  have hX (i : ι) : HasGaussianLaw (X i) P := by
    simpa only [X, smul_eq_mul] using (hh.hasGaussianLaw_circle hε (pt i)).fun_smul γ
  have hm (i : ι) : ∫ ω, X i ω ∂P = 0 := by
    have h := hh.integral_eq_zero (.circle ε (pt i)) hε
    change (∫ ω, hcirc ω ε (pt i) ∂P) = 0 at h
    simp only [X, integral_const_mul, h, mul_zero]
  have hv (i : ι) : variance (X i) P = γ ^ 2 * (-Real.log ε) := by
    rw [show variance (X i) P = cov[X i, X i; P] from
      (covariance_self (hX i).aemeasurable).symm]
    dsimp [X]
    rw [covariance_const_mul_left, covariance_const_mul_right,
      covariance_self (hh.hasGaussianLaw_circle hε (pt i)).aemeasurable,
      hh.variance_circle_inside hε (hpt i)]
    ring
  exact integral_rpow_sum_exp_gaussian_le X hX hm _ hv a ha hp


/-- At a fixed smoothing scale, powers of bounded-mass atomic circle-average
masses form a uniformly integrable family. -/
theorem uniformIntegrable_rpow_sum_circle_atoms
    {Ω J : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ)
    (ι : J → Type*) [∀ j, Fintype (ι j)] (pt : ∀ j, ι j → ℂ)
    (hpt : ∀ j i, ‖pt j i‖ + ε ≤ 1)
    (a : ∀ j, ι j → ℝ) (ha : ∀ j i, 0 ≤ a j i)
    (M : ℝ) (hmass : ∀ j, ∑ i, a j i ≤ M)
    {q : ℝ} (hq : 1 ≤ q) :
    UniformIntegrable (fun j ω => (∑ i, a j i * Real.exp
      (γ * hcirc ω ε (pt j i) - (γ ^ 2 * (-Real.log ε)) / 2)) ^ q) 1 P := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let V := γ ^ 2 * (-Real.log ε)
  let X : J → Ω → ℝ := fun j ω => ∑ i, a j i * Real.exp
    (γ * hcirc ω ε (pt j i) - V / 2)
  let K : ℝ := M ^ (2*q) * Real.exp (((2*q) ^ 2 - 2*q) * V / 2)
  have hX0 (j ω) : 0 ≤ X j ω := Finset.sum_nonneg (fun i _ =>
    mul_nonneg (ha j i) (Real.exp_pos _).le)
  have hI (j) (p : ℝ) (hp : 0 < p) : Integrable (fun ω => X j ω ^ p) P := by
    apply integrable_rpow_sum_exp_gaussian (fun i ω => γ * hcirc ω ε (pt j i)) _
      (a j) (fun _ => V / 2) (ha j) hp
    intro i
    simpa only [smul_eq_mul] using (hh.hasGaussianLaw_circle hε (pt j i)).fun_smul γ
  have hsq (j) : Integrable (fun ω => (X j ω ^ q) ^ 2) P := by
    convert hI j (2*q) (by linarith) using 1
    funext ω
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hX0 j ω)]
    congr 1
    ring
  have hbound (j) : (∫ ω, (X j ω ^ q) ^ 2 ∂P) ≤ K := by
    have hh' := integral_rpow_sum_circle_atoms_le hh hε γ (pt j) (hpt j)
      (a j) (ha j) (p := 2*q) (by linarith)
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


/-- A rescaled reference-square circle lies in the unit disc. -/
theorem norm_annularSquare_rescaled_add_le_one {r δ : ℝ}
    (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) {w : ℂ}
    (hw : w ∈ LatticeProb.LQG.lqgSquare) :
    ‖(((4 * r : ℝ) : ℂ) * w + LatticeProb.dyadicSquareCentre r i)‖ + 4 * r * δ ≤ 1 := by
  have hw' : ‖w‖ ≤ 1 / 4 := by
    simpa using LatticeProb.LQG.lqgSquare_subset_closedBall hw
  have hc := norm_dyadicSquareCentre_add_four_mul_le_one hr hr10 hi
  have ht := norm_add_le (((4 * r : ℝ) : ℂ) * w) (LatticeProb.dyadicSquareCentre r i)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 4 * r)] at ht
  nlinarith

/-- Variance of a scalar multiple of a circle average inside the unit disc. -/
theorem variance_mul_circle_inside {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    {z : ℂ} (hz : ‖z‖ + ε ≤ 1) (γ : ℝ) :
    variance (fun ω => γ * hcirc ω ε z) P = γ ^ 2 * (-Real.log ε) := by
  have hg : HasGaussianLaw (fun ω => γ * hcirc ω ε z) P := by
    simpa only [smul_eq_mul] using (hh.hasGaussianLaw_circle hε z).fun_smul γ
  rw [← covariance_self hg.aemeasurable, covariance_const_mul_left,
    covariance_const_mul_right, covariance_self (hh.hasGaussianLaw_circle hε z).aemeasurable,
    hh.variance_circle_inside hε hz]
  ring

/-- Almost-sure limits of atomic masses preserve the square scaling comparison. -/
theorem integral_rpow_annularSquare_le_of_ae_atomic_tendsto
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ)
    (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (pt : ∀ n, ι n → ℂ)
    (hpt : ∀ n j, pt n j ∈ LatticeProb.LQG.lqgSquare)
    (a : ∀ n, ι n → ℝ) (ha : ∀ n j, 0 ≤ a n j)
    (M : ℝ) (hmass : ∀ n, ∑ j, a n j ≤ M) {q : ℝ} (hq : 1 ≤ q)
    (F G : Ω → ℝ)
    (hF : ∀ᵐ ω ∂P, Tendsto (fun n => ∑ j, a n j * Real.exp
      (γ * hcirc ω (4 * r * δ)
        (((4 * r : ℝ) : ℂ) * pt n j + LatticeProb.dyadicSquareCentre r i) -
        (γ ^ 2 * (-Real.log (4 * r * δ))) / 2)) atTop (𝓝 (F ω)))
    (hG : ∀ᵐ ω ∂P, Tendsto (fun n => ∑ j, a n j * Real.exp
      (γ * hcirc ω δ (pt n j) - (γ ^ 2 * (-Real.log δ)) / 2)) atTop (𝓝 (G ω))) :
    Integrable (fun ω => F ω ^ q) P ∧ Integrable (fun ω => G ω ^ q) P ∧
      (∫ ω, F ω ^ q ∂P) ≤
        Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) *
          ∫ ω, G ω ^ q ∂P := by
  classical
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let z : ∀ n, ι n → ℂ := fun n j =>
    (((4 * r : ℝ) : ℂ) * pt n j + LatticeProb.dyadicSquareCentre r i)
  let X : ℕ → Ω → ℝ := fun n ω => (∑ j, a n j * Real.exp
      (γ * hcirc ω (4 * r * δ) (z n j) -
        (γ ^ 2 * (-Real.log (4 * r * δ))) / 2)) ^ q
  let Y : ℕ → Ω → ℝ := fun n ω => (∑ j, a n j * Real.exp
      (γ * hcirc ω δ (pt n j) - (γ ^ 2 * (-Real.log δ)) / 2)) ^ q
  have hz (n j) : ‖z n j‖ + 4 * r * δ ≤ 1 :=
    norm_annularSquare_rescaled_add_le_one hr hr10 hδ2 hi (hpt n j)
  have hw (n j) : ‖pt n j‖ + δ ≤ 1 := by
    have h : ‖pt n j‖ ≤ 1 / 4 := by
      simpa using LatticeProb.LQG.lqgSquare_subset_closedBall (hpt n j)
    linarith
  have hε : 0 < 4 * r * δ := by positivity
  have hUIX : UniformIntegrable X 1 P :=
    uniformIntegrable_rpow_sum_circle_atoms hh hε γ ι z hz a ha M hmass hq
  have hUIY : UniformIntegrable Y 1 P :=
    uniformIntegrable_rpow_sum_circle_atoms hh hδ γ ι pt hw a ha M hmass hq
  have hFX : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (F ω ^ q)) := by
    filter_upwards [hF] with ω hω
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ q)).continuousAt.tendsto.comp hω
  have hGY : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (G ω ^ q)) := by
    filter_upwards [hG] with ω hω
    exact (Real.continuous_rpow_const (by linarith : 0 ≤ q)).continuousAt.tendsto.comp hω
  have hFi := hUIX.integrable_of_ae_tendsto hFX
  have hGi := hUIY.integrable_of_ae_tendsto hGY
  have hXL := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl (by simp)
    (fun n => hUIX.aestronglyMeasurable n) (memLp_one_iff_integrable.mpr hFi) hUIX.1 hFX
  have hYL := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl (by simp)
    (fun n => hUIY.aestronglyMeasurable n) (memLp_one_iff_integrable.mpr hGi) hUIY.1 hGY
  have hXI := tendsto_integral_of_L1' (fun ω => F ω ^ q)
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hUIX.memLp n))) hXL
  have hYI := tendsto_integral_of_L1' (fun ω => G ω ^ q)
    (Eventually.of_forall (fun n => memLp_one_iff_integrable.mp (hUIY.memLp n))) hYL
  refine ⟨hFi, hGi, le_of_tendsto_of_tendsto hXI (tendsto_const_nhds.mul hYI) ?_⟩
  apply Eventually.of_forall
  intro n
  have hc := integral_rpow_annularSquare_atoms_le_nonneg hh hr hr10 hδ hδ2 hi γ
    (pt n) (hpt n) (a n) (ha n) hq
  dsimp only at hc
  have hvx (j : ι n) : variance (fun ω => γ * hcirc ω (4 * r * δ) (z n j)) P =
      γ ^ 2 * (-Real.log (4 * r * δ)) := variance_mul_circle_inside hh hε (hz n j) γ
  have hvy (j : ι n) : variance (fun ω => γ * hcirc ω δ (pt n j)) P =
      γ ^ 2 * (-Real.log δ) := variance_mul_circle_inside hh hδ (hw n j) γ
  dsimp only [z] at hvx
  simp only [hvx, hvy] at hc
  exact hc



/-- Fixed-scale moment comparison for a finite measure on a grid square. -/
theorem integral_rpow_annularSquare_le_of_finite_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ)
    (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hν : ∀ᵐ z ∂ν, z ∈ LatticeProb.LQG.lqgSquare) {q : ℝ} (hq : 1 ≤ q) :
    let F : Ω → ℝ := fun ω => ∫ z, Real.exp
      (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * z + LatticeProb.dyadicSquareCentre r i) -
        γ ^ 2 * (-Real.log (4 * r * δ)) / 2) ∂ν
    let G : Ω → ℝ := fun ω => ∫ z, Real.exp
      (γ * hcirc ω δ z - γ ^ 2 * (-Real.log δ) / 2) ∂ν
    Integrable (fun ω => F ω ^ q) P ∧ Integrable (fun ω => G ω ^ q) P ∧
      (∫ ω, F ω ^ q ∂P) ≤
        Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * ∫ ω, G ω ^ q ∂P := by
  classical
  have hK : IsCompact LatticeProb.LQG.lqgSquare := by
    have hc : IsClosed LatticeProb.LQG.lqgSquare := by
      have hre : Continuous fun w : ℂ => |w.re| := Complex.continuous_re.abs
      have him : Continuous fun w : ℂ => |w.im| := Complex.continuous_im.abs
      exact (isClosed_le hre continuous_const).inter (isClosed_le him continuous_const)
    exact (isCompact_closedBall (0 : ℂ) (1 / 4)).of_isClosed_subset hc
      LatticeProb.LQG.lqgSquare_subset_closedBall
  have h0 : (0 : ℂ) ∈ LatticeProb.LQG.lqgSquare := by simp [LatticeProb.LQG.lqgSquare]
  let T := fun n => SimpleFunc.approxOn id measurable_id LatticeProb.LQG.lqgSquare 0 h0 n
  let ι : ℕ → Type := fun n => ↥(T n).range
  let pt : ∀ n, ι n → ℂ := fun _ j => j.1
  let a : ∀ n, ι n → ℝ := fun n j => ν.real ((T n) ⁻¹' {j.1})
  have hpt : ∀ n j, pt n j ∈ LatticeProb.LQG.lqgSquare := by
    intro n j
    obtain ⟨z, hz⟩ := SimpleFunc.mem_range.mp j.2
    change j.1 ∈ LatticeProb.LQG.lqgSquare
    rw [← hz]
    exact SimpleFunc.approxOn_mem measurable_id h0 n z
  have ha : ∀ n j, 0 ≤ a n j := fun _ _ => ENNReal.toReal_nonneg
  have hmass : ∀ n, ∑ j, a n j ≤ ν.real univ := by
    intro n
    apply le_of_eq
    change (∑ j : ↥(T n).range, ν.real ((T n) ⁻¹' {j.1})) = ν.real univ
    calc
      _ = ∑ z ∈ (T n).range, ν.real ((T n) ⁻¹' {z}) :=
        Finset.sum_coe_sort (T n).range (fun z : ℂ => ν.real ((T n) ⁻¹' {z}))
      _ = _ := by
        simp only [measureReal_def, ← ENNReal.toReal_sum (fun z _ => measure_ne_top ν _),
          (T n).sum_range_measure_preimage_singleton]
  have hquad (f : ℂ → ℝ) (hf : Continuous f) :
      Tendsto (fun n => ∑ j, a n j * f (pt n j)) atTop (𝓝 (∫ z, f z ∂ν)) := by
    have h := tendsto_sum_fiber_mass_mul hK h0 ν hν f hf
    convert h using 1
    ext n
    exact Finset.sum_coe_sort (T n).range (fun z : ℂ => ν.real ((T n) ⁻¹' {z}) * f z)
  have hε : 0 < 4 * r * δ := by positivity
  apply integral_rpow_annularSquare_le_of_ae_atomic_tendsto hh hr hr10 hδ hδ2 hi γ
    ι pt hpt a ha (ν.real univ) hmass hq
  · filter_upwards [hh.ae_continuous_circle_fixed hε] with ω hω
    have htest : Continuous (fun z : ℂ => Real.exp
        (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * z + LatticeProb.dyadicSquareCentre r i) -
          γ ^ 2 * (-Real.log (4 * r * δ)) / 2)) := by fun_prop
    exact hquad _ htest
  · filter_upwards [hh.ae_continuous_circle_fixed hδ] with ω hω
    have htest : Continuous (fun z : ℂ => Real.exp
        (γ * hcirc ω δ z - γ ^ 2 * (-Real.log δ) / 2)) := by fun_prop
    exact hquad _ htest



/-- The reference-square image of an annular grid-square occupation measure. -/
noncomputable def annularSquareOccupation (b : ContinuousPath ℂ) (u v δ r : ℝ)
    (i : ℤ × ℤ) : Measure ℂ :=
  Measure.map (fun t : ℝ => (b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ))
    (volume.restrict (Ioc u v ∩ annularSquareTimeSet b δ r i))

instance (b : ContinuousPath ℂ) (u v δ r : ℝ) (i : ℤ × ℤ) :
    IsFiniteMeasure (annularSquareOccupation b u v δ r i) := by
  dsimp [annularSquareOccupation]
  let : IsFiniteMeasure (volume.restrict (Ioc u v ∩ annularSquareTimeSet b δ r i)) :=
    isFiniteMeasure_of_le (volume.restrict (Ioc u v))
      (Measure.restrict_mono_set volume inter_subset_left)
  infer_instance

/-- The rescaled annular occupation measure is carried by the reference square. -/
theorem ae_mem_annularSquareOccupation (b : ContinuousPath ℂ) (u v δ : ℝ)
    {r : ℝ} (hr : 0 < r) (i : ℤ × ℤ) :
    ∀ᵐ z ∂(annularSquareOccupation b u v δ r i), z ∈ LatticeProb.LQG.lqgSquare := by
  let g : ℝ → ℂ := fun t => (b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hQ : MeasurableSet LatticeProb.LQG.lqgSquare := by
    apply IsClosed.measurableSet
    have hre : Continuous fun w : ℂ => |w.re| := Complex.continuous_re.abs
    have him : Continuous fun w : ℂ => |w.im| := Complex.continuous_im.abs
    exact (isClosed_le hre continuous_const).inter (isClosed_le him continuous_const)
  change ∀ᵐ z ∂(Measure.map g (volume.restrict (Ioc u v ∩ annularSquareTimeSet b δ r i))),
    z ∈ LatticeProb.LQG.lqgSquare
  apply (ae_map_iff (p := fun z => z ∈ LatticeProb.LQG.lqgSquare)
    hg.measurable.aemeasurable hQ).2
  filter_upwards [ae_restrict_mem (measurableSet_Ioc.inter
    (measurableSet_annularSquareTimeSet b δ r i))] with t ht
  exact dyadicSquare_rescaled_mem_lqgSquare hr ht.2.1

/-- Continuous tests of the rescaled occupation measure are time integrals. -/
theorem integral_annularSquareOccupation (b : ContinuousPath ℂ) (u v δ r : ℝ) (i : ℤ × ℤ)
    (f : ℂ → ℝ) (hf : Continuous f) :
    ∫ z, f z ∂(annularSquareOccupation b u v δ r i) =
      ∫ t in Ioc u v ∩ annularSquareTimeSet b δ r i,
        f ((b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)) := by
  apply integral_map
  · fun_prop
  · exact hf.aestronglyMeasurable

/-- Fixed-scale Gaussian comparison for a rescaled annular path occupation measure. -/
theorem integral_rpow_annularSquare_le_of_occupation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ)
    (b : ContinuousPath ℂ) (u v a : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    let ν := annularSquareOccupation b u v a r i
    let F : Ω → ℝ := fun ω => ∫ z, Real.exp
      (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * z + LatticeProb.dyadicSquareCentre r i) -
        γ ^ 2 * (-Real.log (4 * r * δ)) / 2) ∂ν
    let G : Ω → ℝ := fun ω => ∫ z, Real.exp
      (γ * hcirc ω δ z - γ ^ 2 * (-Real.log δ) / 2) ∂ν
    Integrable (fun ω => F ω ^ q) P ∧ Integrable (fun ω => G ω ^ q) P ∧
      (∫ ω, F ω ^ q ∂P) ≤
        Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * ∫ ω, G ω ^ q ∂P := by
  exact integral_rpow_annularSquare_le_of_finite_measure hh hr hr10 hδ hδ2 hi γ _
    (ae_mem_annularSquareOccupation b u v a hr i) hq

/-- Fixed-scale comparison for the time spent in an annular grid square. -/
theorem integral_rpow_annularSquare_le_of_time_integrals
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ)
    (b : ContinuousPath ℂ) (u v a : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    let g : ℝ → ℂ := fun t => (b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)
    let I := Ioc u v ∩ annularSquareTimeSet b a r i
    let F : Ω → ℝ := fun ω => ∫ t in I, Real.exp
      (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * g t + LatticeProb.dyadicSquareCentre r i) -
        γ ^ 2 * (-Real.log (4 * r * δ)) / 2)
    let G : Ω → ℝ := fun ω => ∫ t in I, Real.exp
      (γ * hcirc ω δ (g t) - γ ^ 2 * (-Real.log δ) / 2)
    Integrable (fun ω => F ω ^ q) P ∧ Integrable (fun ω => G ω ^ q) P ∧
      (∫ ω, F ω ^ q ∂P) ≤
        Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * ∫ ω, G ω ^ q ∂P := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let ν := annularSquareOccupation b u v a r i
  let g : ℝ → ℂ := fun t => (b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)
  let I := Ioc u v ∩ annularSquareTimeSet b a r i
  let F : Ω → ℝ := fun ω => ∫ z, Real.exp
    (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * z + LatticeProb.dyadicSquareCentre r i) -
      γ ^ 2 * (-Real.log (4 * r * δ)) / 2) ∂ν
  let G : Ω → ℝ := fun ω => ∫ z, Real.exp
    (γ * hcirc ω δ z - γ ^ 2 * (-Real.log δ) / 2) ∂ν
  let Ftime : Ω → ℝ := fun ω => ∫ t in I, Real.exp
    (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * g t + LatticeProb.dyadicSquareCentre r i) -
      γ ^ 2 * (-Real.log (4 * r * δ)) / 2)
  let Gtime : Ω → ℝ := fun ω => ∫ t in I, Real.exp
    (γ * hcirc ω δ (g t) - γ ^ 2 * (-Real.log δ) / 2)
  have hε : 0 < 4 * r * δ := by positivity
  have hF : F =ᵐ[P] Ftime := by
    filter_upwards [hh.ae_continuous_circle_fixed hε] with ω hω
    apply integral_annularSquareOccupation
    fun_prop
  have hG : G =ᵐ[P] Gtime := by
    filter_upwards [hh.ae_continuous_circle_fixed hδ] with ω hω
    apply integral_annularSquareOccupation
    fun_prop
  have h := integral_rpow_annularSquare_le_of_occupation hh hr hr10 hδ hδ2 hi γ b u v a hq
  change Integrable (fun ω => F ω ^ q) P ∧ Integrable (fun ω => G ω ^ q) P ∧
    (∫ ω, F ω ^ q ∂P) ≤
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * ∫ ω, G ω ^ q ∂P at h
  have hFq : (fun ω => F ω ^ q) =ᵐ[P] (fun ω => Ftime ω ^ q) :=
    hF.mono (fun _ h => congrArg (fun z : ℝ => z ^ q) h)
  have hGq : (fun ω => G ω ^ q) =ᵐ[P] (fun ω => Gtime ω ^ q) :=
    hG.mono (fun _ h => congrArg (fun z : ℝ => z ^ q) h)
  exact ⟨h.1.congr hFq, h.2.1.congr hGq, by
    rw [← integral_congr_ae hFq, ← integral_congr_ae hGq]
    exact h.2.2⟩


/-- The log-variance normalization equals the circle-average GMC density. -/
theorem gmcDensity_eq_exp_normalized {Ω : Type*} (hcirc : Ω → ℝ → ℂ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (z : ℂ) (ω : Ω) :
    LatticeProb.Gauss.gmcDensity hcirc γ ε z ω =
      Real.exp (γ * hcirc ω ε z - γ ^ 2 * (-Real.log ε) / 2) := by
  rw [LatticeProb.Gauss.gmcDensity, Real.rpow_def_of_pos hε, ← Real.exp_add]
  congr 1
  ring

/-- The nonnegative time integral equals the extended occupation mass. -/
theorem ofReal_integral_annularSquare_gmcDensity_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ : ℝ) (b : ContinuousPath ℂ)
    (u v a r : ℝ) (i : ℤ × ℤ) :
    ∀ᵐ ω ∂P, ENNReal.ofReal (∫ t in annularSquareTimeSet b a r i ∩ Ioc u v,
      LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) =
      ∫⁻ t in annularSquareTimeSet b a r i ∩ Ioc u v,
        ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) := by
  filter_upwards [hh.ae_continuous_circle_fixed hε] with ω hω
  have hc : Continuous (fun t : ℝ => LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω) := by
    simp only [LatticeProb.Gauss.gmcDensity]
    fun_prop
  have hi : IntegrableOn (fun t : ℝ => LatticeProb.Gauss.gmcDensity hcirc γ ε (b t.toNNReal) ω)
      (annularSquareTimeSet b a r i ∩ Ioc u v) :=
    hc.integrableOn_Ioc.mono_set inter_subset_right
  exact ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun t => LatticeProb.Gauss.gmcDensity_nonneg hcirc hε γ _ _)

/-- The annular-square scaling comparison bounds the extended GMC occupation moment. -/
theorem lintegral_rpow_annularSquare_gmcDensity_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {r δ : ℝ} (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    {i : ℤ × ℤ} (hi : i ∈ LatticeProb.squareIndex r) (γ : ℝ)
    (b : ContinuousPath ℂ) (u v a : ℝ) {q : ℝ} (hq : 1 ≤ q) :
    let T := annularSquareTimeSet b a r i ∩ Ioc u v
    let G : Ω → ℝ := fun ω => ∫ t in T, Real.exp
      (γ * hcirc ω δ ((b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)) -
        γ ^ 2 * (-Real.log δ) / 2)
    (∫⁻ ω, (∫⁻ t in T, ENNReal.ofReal
      (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q ∂P) ≤
      ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ENNReal.ofReal (∫ ω, G ω ^ q ∂P) := by
  let T := annularSquareTimeSet b a r i ∩ Ioc u v
  let g : ℝ → ℂ := fun t => (b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)
  let F : Ω → ℝ := fun ω => ∫ t in T, Real.exp
    (γ * hcirc ω (4 * r * δ) (((4 * r : ℝ) : ℂ) * g t + LatticeProb.dyadicSquareCentre r i) -
      γ ^ 2 * (-Real.log (4 * r * δ)) / 2)
  let G : Ω → ℝ := fun ω => ∫ t in T, Real.exp
    (γ * hcirc ω δ (g t) - γ ^ 2 * (-Real.log δ) / 2)
  have hε : 0 < 4 * r * δ := by positivity
  have hR : (((4 * r : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (show 4 * r ≠ 0 by positivity)
  have hF (ω : Ω) : F ω = ∫ t in T,
      LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω := by
    apply integral_congr_ae
    filter_upwards [] with t
    rw [gmcDensity_eq_exp_normalized hcirc hε]
    dsimp only [g]
    rw [mul_div_cancel₀ _ hR, sub_add_cancel]
  have hnonneg (ω : Ω) : 0 ≤ F ω := integral_nonneg (fun t => (Real.exp_pos _).le)
  have ht := integral_rpow_annularSquare_le_of_time_integrals hh hr hr10 hδ hδ2 hi γ b u v a hq
  dsimp only at ht
  simp only [inter_comm (Ioc u v) (annularSquareTimeSet b a r i)] at ht
  change Integrable (fun ω => F ω ^ q) P ∧ Integrable (fun ω => G ω ^ q) P ∧
    (∫ ω, F ω ^ q ∂P) ≤
      Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2) * ∫ ω, G ω ^ q ∂P at ht
  have heq : ENNReal.ofReal (∫ ω, F ω ^ q ∂P) =
      ∫⁻ ω, (∫⁻ t in T, ENNReal.ofReal
        (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal ht.1
      (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (hnonneg ω) q)]
    apply lintegral_congr_ae
    filter_upwards [ofReal_integral_annularSquare_gmcDensity_eq hh hε γ b u v a r i] with ω hω
    rw [← ENNReal.ofReal_rpow_of_nonneg (hnonneg ω) (by linarith : 0 ≤ q), hF ω, hω]
  dsimp only
  rw [← heq, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact ENNReal.ofReal_le_ofReal ht.2.2

/-- The annular moment is bounded by rescaled square moments and separated interactions. -/
theorem lintegral_annular_mass_rpow_le_rescaled_square_moments_add_far
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (b : ContinuousPath ℂ) (u v a : ℝ) {r δ : ℝ}
    (hr : 0 < r) (hr10 : r ≤ 1 / 10) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (γ : ℝ)
    {q : ℝ} (hq : 1 ≤ q) (hq2 : q ≤ 2) :
    let S := LatticeProb.squareIndex r
    let T := fun i => annularSquareTimeSet b a r i ∩ Ioc u v
    let G := fun i ω => ∫ t in T i, Real.exp
      (γ * hcirc ω δ ((b t.toNNReal - LatticeProb.dyadicSquareCentre r i) / (4 * r : ℝ)) -
        γ ^ 2 * (-Real.log δ) / 2)
    (∫⁻ ω, (∫⁻ t in {t | a ≤ ‖b t.toNNReal‖ ∧ ‖b t.toNNReal‖ ≤ 1 / 2} ∩ Ioc u v,
      ENNReal.ofReal (LatticeProb.Gauss.gmcDensity hcirc γ (4 * r * δ) (b t.toNNReal) ω)) ^ q ∂P) ≤
      18 * (∑ i ∈ S, ENNReal.ofReal (Real.exp (q * (q - 1) * (-γ ^ 2 * Real.log (4 * r)) / 2)) *
        ENNReal.ofReal (∫ ω, G i ω ^ q ∂P)) +
      ∑ i ∈ S, ∑ j ∈ S.filter (fun j => ¬ squareGridAdjacent i j),
        (ENNReal.ofReal ((2 / r) ^ (γ ^ 2)) * (volume (T i) * volume (T j))) ^ (q / 2) := by
  classical
  have hε : 0 < 4 * r * δ := by positivity
  have hε2 : 4 * r * δ ≤ 1 / 2 := by nlinarith
  have hb := lintegral_annular_mass_rpow_le_square_moments_add_far hh b u v a hε hε2 hr γ
    (by linarith : 0 < q) hq2
  dsimp only at hb ⊢
  refine hb.trans (add_le_add ?_ le_rfl)
  gcongr with i hi
  exact lintegral_rpow_annularSquare_gmcDensity_le hh hr hr10 hδ hδ2 hi γ b u v a hq

/-- A nonnegative integral over a measurable time set under positive dilation. -/
theorem lintegral_time_dilation {c : ℝ} (hc : 0 < c) (A : Set ℝ) (hA : MeasurableSet A)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ t in A, f t) = ENNReal.ofReal c * ∫⁻ s in (fun s : ℝ => c * s) ⁻¹' A, f (c * s) := by
  have hm : Measurable (fun t : ℝ => c⁻¹ * t) := by fun_prop
  have hmap : Measure.map (fun t : ℝ => c⁻¹ * t) volume = ENNReal.ofReal c • volume := by
    rw [Real.map_volume_mul_left (inv_ne_zero hc.ne'), inv_inv, abs_of_pos hc]
  let g : ℝ → ℝ≥0∞ := fun s => A.indicator f (c * s)
  have hg : Measurable g := (hf.indicator hA).comp (measurable_const_mul c)
  have heq : (∫⁻ s, g s ∂Measure.map (fun t : ℝ => c⁻¹ * t) volume) =
      ∫⁻ t in A, f t := by
    rw [lintegral_map hg hm]
    simp only [g, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul, lintegral_indicator hA]
  rw [hmap, lintegral_smul_measure] at heq
  rw [← heq]
  congr 1
  rw [← lintegral_indicator (hA.preimage (measurable_const_mul c))]
  apply lintegral_congr
  intro s
  by_cases hs : c * s ∈ A <;> simp [g, hs]

/-- Rescaling space and time preserves restricted path occupation integrals. -/
theorem lintegral_rescaled_path_occupation (x z : ℂ) (c : ℝ≥0) (hc : 0 < c) (b : ContinuousPath ℂ)
    (A : Set ℝ) (hA : MeasurableSet A) (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ t in A, φ ((b t.toNNReal - z) / (Real.sqrt c : ℂ))) =
      ENNReal.ofReal c * ∫⁻ s in (fun s : ℝ => (c : ℝ) * s) ⁻¹' A,
        φ (scaledCenteredPlanarPath x c b s.toNNReal +
          (x - z) / (Real.sqrt c : ℂ)) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hf : Measurable (fun t : ℝ => φ ((b t.toNNReal - z) / (Real.sqrt c : ℂ))) := by
    apply hφ.comp
    fun_prop
  rw [lintegral_time_dilation hcR A hA _ hf]
  congr 1
  apply lintegral_congr
  intro s
  congr 1
  have ht : Real.toNNReal ((c : ℝ) * s) = c * Real.toNNReal s := by
    rw [Real.toNNReal_mul (by positivity : (0 : ℝ) ≤ c), Real.toNNReal_coe]
  rw [ht]
  simp only [scaledCenteredPlanarPath, ContinuousMap.coe_mk]
  simp only [div_eq_mul_inv, Complex.real_smul, Complex.ofReal_inv]
  ring


/-- Brownian scaling transfers restricted occupation moments to the standard law. -/
theorem lintegral_planarBrownianMotion_rescaled_occupation_rpow (x z : ℂ) (c : ℝ≥0) (hc : 0 < c)
    (A : Set ℝ) (hA : MeasurableSet A) (φ : ℂ → ℝ≥0∞) (hφ : Measurable φ)
    (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ b, (∫⁻ t in A, φ ((b t.toNNReal - z) / (Real.sqrt c : ℂ))) ^ q
      ∂planarBrownianMotion x) =
    (ENNReal.ofReal c) ^ q * ∫⁻ b,
      (∫⁻ s in (fun s : ℝ => (c : ℝ) * s) ⁻¹' A,
        φ (b s.toNNReal + (x - z) / (Real.sqrt c : ℂ))) ^ q
      ∂planarBrownianMotion 0 := by
  let B : Set ℝ := (fun s : ℝ => (c : ℝ) * s) ⁻¹' A
  let F : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
    (∫⁻ s in B, φ (b s.toNNReal + (x - z) / (Real.sqrt c : ℂ))) ^ q
  have hF : Measurable F := by
    dsimp [F]
    apply Measurable.pow_const
    apply Measurable.lintegral_prod_right
    apply hφ.comp
    fun_prop
  calc
    _ = ∫⁻ b, (ENNReal.ofReal c) ^ q * F (scaledCenteredPlanarPath x c b)
        ∂planarBrownianMotion x := by
      apply lintegral_congr
      intro b
      rw [lintegral_rescaled_path_occupation x z c hc b A hA φ hφ,
        ENNReal.mul_rpow_of_nonneg _ _ hq]
    _ = (ENNReal.ofReal c) ^ q * ∫⁻ b, F (scaledCenteredPlanarPath x c b)
        ∂planarBrownianMotion x := by
      simpa only [Function.comp_def] using
        (lintegral_const_mul ((ENNReal.ofReal c) ^ q)
          (hF.comp (continuous_scaledCenteredPlanarPath x c).measurable))
    _ = _ := by
      rw [← lintegral_map hF (continuous_scaledCenteredPlanarPath x c).measurable,
        planarBrownianMotion_map_scaledCenteredPlanarPath x hc.ne']

end HarmonicBalls
