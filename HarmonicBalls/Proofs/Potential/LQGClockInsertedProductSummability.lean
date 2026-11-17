import HarmonicBalls.Proofs.Potential.LQGClockInsertedFixedConvergence

/-! # Product-law cutoff increments

Jointly measurable versions transfer fixed-cutoff summability to the product law.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped ENNReal NNReal
namespace HarmonicBalls

private theorem measurable_unit_path_integral {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω × ℂ → ℝ) (hF : Measurable F) :
    Measurable (fun q : ContinuousPath ℂ × Ω =>
      ∫ z, F (q.2, z) ∂(Measure.map (fun t => q.1 t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
    heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hG : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => F (q.1.2, q.1.1 q.2)) :=
    hF.comp ((measurable_snd.comp measurable_fst).prodMk heval)
  have hm := hG.stronglyMeasurable.integral_prod_right' (ν := ν)
  convert hm.measurable using 1
  funext q
  exact integral_map q.1.continuous.measurable.aemeasurable
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

/-- Closed-cutoff dyadic increments admit jointly measurable versions, with
one field event for all paths and indices. -/
theorem exists_measurable_inserted_closedBall_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∃ F : ℕ → ContinuousPath ℂ × Ω → ℝ, (∀ n, Measurable (F n)) ∧
      ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (n : ℕ),
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        F n (b, ω) = ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z
          ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let E : Set ℂ := {z | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}
  have hE : MeasurableSet E :=
    (measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le measurable_norm measurable_const)
  let ε : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  let G : ℕ → Ω × ℂ → ℝ := fun n q => E.indicator (fun z =>
    (ε n/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε n/2) z-H q.1 1 0 - α*Real.log (max (ε n/2) ‖z‖))) -
    (ε n)^(γ^2/2) * Real.exp (γ*(H q.1 (ε n) z-H q.1 1 0 - α*Real.log (max (ε n) ‖z‖)))) q.2
  have hG (n : ℕ) : Measurable (G n) := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε n/2) q.2) :=
      (hHm (ε n/2) (half_pos (hε n))).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 (ε n) q.2) :=
      (hHm (ε n) (hε n)).comp measurable_swap
    have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    apply Measurable.indicator _ (hE.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  refine ⟨fun n q => ∫ z, G n (q.2,z) ∂(Measure.map (fun t => q.1 t)
    (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))),
    fun n => measurable_unit_path_integral (G n) (hG n), ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hr b n
  apply integral_congr_ae
  filter_upwards with z
  simp only [G, Set.indicator_apply]
  split_ifs
  · rw [hω, hω, hω, hr (ε n/2) z (half_pos (hε n)), hr (ε n) z (hε n)]
  · rfl

/-- For each fixed cutoff and start, the actual inserted dyadic closed-cutoff
increments are summable almost surely under the field-path product law. -/
theorem ae_prod_summable_inserted_closedBall_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) (δ : ℝ) :
    ∀ᵐ q : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      let μ := Measure.map (fun t => q.2 t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) z ∂μ|) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_inserted_closedBall_increments hh γ α δ
  let S : Set (ContinuousPath ℂ × Ω) :=
    {q | (∑' n, ENNReal.ofReal |F n q|) < ∞}
  have hS : MeasurableSet S :=
    measurableSet_lt (Measurable.tsum (fun n => (hFm n).abs.ennreal_ofReal)) measurable_const
  have hiter : ∀ᵐ b ∂planarBrownianMotion x, ∀ᵐ ω ∂P, (b, ω) ∈ S := by
    filter_upwards [planarBrownianMotion_ae_field_ae_summable_inserted_closedBall_increments
      hh x hq0 hq2 hγ hsub] with b hb
    filter_upwards [hb δ, hFae] with ω hsum hω
    have hsumF : Summable (fun n => |F n (b,ω)|) := by
      apply hsum.congr
      intro n
      rw [hω b n]
    change (∑' n, ENNReal.ofReal |F n (b,ω)|) < ∞
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => abs_nonneg _) hsumF]
    exact ENNReal.ofReal_lt_top
  have hprod : ∀ᵐ q ∂((planarBrownianMotion x).prod P), q ∈ S :=
    (Measure.ae_prod_iff_ae_ae hS).2 hiter
  have hactual : ∀ᵐ q : ContinuousPath ℂ × Ω ∂((planarBrownianMotion x).prod P),
      let μ := Measure.map (fun t => q.1 t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z ∂μ|) := by
    filter_upwards [hprod, (Measure.quasiMeasurePreserving_snd
      (μ := planarBrownianMotion x) (ν := P)).ae hFae] with q hq hω
    have hsum := ENNReal.summable_toReal (ne_of_lt hq)
    apply hsum.congr
    intro n
    rw [ENNReal.toReal_ofReal (abs_nonneg _), hω q.1 n]
  exact (Measure.measurePreserving_swap (μ := P)
    (ν := planarBrownianMotion x)).quasiMeasurePreserving.ae hactual


/-- For each fixed cutoff and start, the actual inserted dyadic closed-cutoff
increments are summable for almost every field and then almost every path. -/
theorem ae_field_ae_brownian_summable_inserted_closedBall_increments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) (δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      let μ := Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
      Summable (fun n : ℕ =>
        let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
        |∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z ∂μ|) := by
  exact Measure.ae_ae_of_ae_prod
    (ae_prod_summable_inserted_closedBall_increments hh x hq0 hq2 hγ hsub δ)


end HarmonicBalls
