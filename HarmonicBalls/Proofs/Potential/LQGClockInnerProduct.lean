import HarmonicBalls.Proofs.Potential.LQGClockInnerFirstMoment
import HarmonicBalls.Proofs.Potential.LQGClockAnnularUniformIncrement

/-! # Product-law inner clock occupation

Joint measurability and first moments for inserted clock occupation near the origin.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- An inner clock cell is jointly measurable in the field and Brownian path. -/
theorem measurable_inner_clock_cell {Ω : Type*} [MeasurableSpace Ω]
    (H : Ω → ℝ → ℂ → ℝ) {ε : ℝ} (hε : 0 < ε) (γ α δ a b : ℝ)
    (hH : ∀ r : ℝ, 0 < r → Measurable (fun p : Ω × ℂ => H p.1 r p.2)) :
    Measurable (fun p : Ω × ContinuousPath ℂ =>
      ∫⁻ s in Ioc a b, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.1 ε z - H p.1 1 0 -
            α * Real.log (max ε ‖z‖)))) (p.2 s.toNNReal))) := by
  have hev : Measurable fun p : (Ω × ContinuousPath ℂ) × ℝ => p.1.2 p.2.toNNReal :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable.comp
      (measurable_fst.snd.prodMk measurable_snd)
  have h1 : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => H p.1.1 1 0) :=
    (hH 1 zero_lt_one).comp (measurable_fst.fst.prodMk measurable_const)
  have he : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ => H p.1.1 ε (p.1.2 p.2.toNNReal)) :=
    (hH ε hε).comp (measurable_fst.fst.prodMk hev)
  have hA : MeasurableSet {z : ℂ | ‖z‖ < δ} :=
    measurableSet_lt measurable_norm measurable_const
  have hf : Measurable (fun p : (Ω × ContinuousPath ℂ) × ℝ =>
      ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
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

/-- A jointly measurable inner cell version agrees with the inserted-field cell
on one field event, simultaneously for positive scales, paths, and intervals. -/
theorem exists_measurable_inner_inserted_clock_cell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (γ α δ : ℝ) :
    ∃ H : Ω → ℝ → ℂ → ℝ,
      (∀ ε : ℝ, 0 < ε → ∀ a b : ℝ,
        Measurable (fun p : Ω × ContinuousPath ℂ =>
          ∫⁻ s in Ioc a b, ENNReal.ofReal
            ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
              ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.1 ε z - H p.1 1 0 -
                α * Real.log (max ε ‖z‖)))) (p.2 s.toNNReal)))) ∧
      (∀ᵐ ω ∂P, ∀ (ε : ℝ), 0 < ε → ∀ (b : ContinuousPath ℂ) (a c : ℝ),
        (∫⁻ s in Ioc a c, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω ε z - H ω 1 0 -
              α * Real.log (max ε ‖z‖)))) (b s.toNNReal))) =
        ∫⁻ s in Ioc a c, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal))) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  refine ⟨H, ?_, ?_⟩
  · intro ε hε a b
    apply HarmonicBalls.measurable_inner_clock_cell H hε γ α δ a b
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

/-- The actual inserted inner clock cell is almost everywhere measurable
under the product of the field law and an s-finite path law. -/
theorem aemeasurable_inner_inserted_clock_cell {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure (ContinuousPath ℂ)) [SFinite ν]
    {ε : ℝ} (hε : 0 < ε) (γ α δ a b : ℝ) :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      ∫⁻ s in Ioc a b, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)))
      (P.prod ν) := by
  obtain ⟨H, hHm, hHae⟩ := HarmonicBalls.exists_measurable_inner_inserted_clock_cell hh γ α δ
  apply (hHm ε hε a b).aemeasurable.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hHae] with p hp
  exact hp ε hε p.2 a b

/-- The actual inner clock occupation has a uniform product-law first moment bound. -/
theorem exists_lintegral_prod_brownian_inner_inserted_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {ε δ : ℝ}, 0 < ε → ε ≤ 1/2 →
      0 < δ → δ ≤ 1/2 →
      (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal)))
        ∂(P.prod (planarBrownianMotion x))) ≤ (ENNReal.ofReal δ) ^ (p - γ * α) * C := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ := planarBrownianMotion_inner_inserted_density_le hh x γ α p hq hqp hp
  refine ⟨C, hC, ?_⟩
  intro ε δ hε hεhalf hδ hδhalf
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let A : Set ℂ := {z : ℂ | ‖z‖ < δ}
  let F : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun q =>
    ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
      (A.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))
  have hF : AEMeasurable F (P.prod (planarBrownianMotion x)) :=
    aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) hε γ α δ 0 1
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hA : MeasurableSet A := measurableSet_lt measurable_norm measurable_const
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
      F (ω,b) = ∫⁻ z, A.indicator (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂(ν.map b) := by
    filter_upwards [hmeas] with ω hω
    have heqfun : (fun z => ENNReal.ofReal (A.indicator (fun w => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε w)) z)) =
        A.indicator (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) := by
      funext z
      simp only [Set.indicator_apply]
      split_ifs <;> simp
    rw [← heqfun, lintegral_map hω b.continuous.measurable]
    dsimp [F, ν]
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    symm
    exact lintegral_map (hω.comp b.continuous.measurable) continuous_real_toNNReal.measurable
  change (∫⁻ q, F q ∂(P.prod (planarBrownianMotion x))) ≤ _
  rw [lintegral_prod_symm _ hF]
  refine (le_of_eq ?_).trans (hbound hε hεhalf hδ hδhalf)
  apply lintegral_congr
  intro b
  apply lintegral_congr_ae
  filter_upwards [heq b] with ω hω
  exact hω

/-- A uniform first moment bounds the probability of a large inner occupation. -/
theorem exists_brownian_inner_inserted_tail_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α p : ℝ) (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {ε δ : ℝ}, 0 < ε → ε ≤ 1/2 →
      0 < δ → δ ≤ 1/2 → ∀ η : ℝ≥0∞,
      η * (P.prod (planarBrownianMotion x)) {q : Ω × ContinuousPath ℂ |
        η ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))} ≤
          (ENNReal.ofReal δ) ^ (p - γ * α) * C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_inner_inserted_le hh x γ α p hq hqp hp
  refine ⟨C, hC, ?_⟩
  intro ε δ hε hεhalf hδ hδhalf η
  exact (mul_meas_ge_le_lintegral₀
    (aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) hε γ α δ 0 1) η).trans
      (hbound hε hεhalf hδ hδhalf)

end HarmonicBalls
