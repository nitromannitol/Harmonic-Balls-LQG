import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridOccupationIncrement
import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.LQGBallMassGrid2

/-! # Annular clocks at continuum smoothing radii

A fine geometric grid controls the annular occupation clock at every positive
smoothing radius in each dyadic shell.
-/

open MeasureTheory Set MarkovProcess Filter LatticeProb.LQG
open LatticeProb.LQG.GMCScaleGrid LatticeProb.LQG.GMCRatioLimit
open scoped Topology NNReal ENNReal

namespace HarmonicBalls

/-- Every radius in a dyadic shell has a nearby grid radius whose annular clock
is relatively close, uniformly in the path and stopped time. -/
theorem ae_eventually_annular_exit_clock_grid_comparison
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) (D : Set ℂ) :
    ∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ s : ℝ,
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        ∃ i ≤ gridCount c k, ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
          let r := gridScale (gridCount c) k i
          let A : ℝ → ℝ := fun v => ∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              v ^ (γ ^ 2 / 2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z)) (b u.toNNReal)
          |A s - A r| ≤ η k * A r := by
  obtain ⟨β, hβ, hmod⟩ :=
    ae_eventually_annular_stopped_occupation_radial_difference_le hh α γ hδ
      (show 0 < c / 4 by positivity) D
  let B : ℕ → ℝ := fun k => |γ| * dyadicScale k ^ β + γ ^ 2 * dyadicScale k ^ (c / 4)
  have hpow (p : ℝ) (hp : 0 < p) : Tendsto (fun k => dyadicScale k ^ p) atTop (𝓝 0) := by
    have h0 : Tendsto dyadicScale atTop (𝓝 (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa [Real.zero_rpow hp.ne'] using h0.rpow_const (Or.inr hp.le)
  have hB : Tendsto B atTop (𝓝 0) := by
    dsimp [B]
    simpa using ((hpow β hβ).const_mul |γ|).add
      ((hpow (c / 4) (by positivity)).const_mul (γ ^ 2))
  refine ⟨fun k => B k * Real.exp (B k), ?_, ?_⟩
  · simpa using hB.mul ((Real.continuous_exp.tendsto 0).comp hB)
  · filter_upwards [hmod] with ω hω
    filter_upwards [hω, eventually_ge_atTop 1] with k hk hk1 s hs1 hs2
    have he : 0 < dyadicScale k := dyadicScale_pos k
    have helt : dyadicScale k < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
    obtain ⟨hN, hmesh⟩ := one_le_gridCount_and_mesh_le hc.le k
    obtain ⟨i, hi, hnear⟩ := exists_gridScale_near (gridCount c) hN hs1 hs2
    obtain ⟨hr1, hr2⟩ := gridScale_mem_Icc (gridCount c) hi
    have hclose : |s - gridScale (gridCount c) k i| < dyadicScale k * dyadicScale k ^ (c / 4) :=
      (hnear.trans hmesh).trans_lt (mul_lt_mul_of_pos_left
        (Real.rpow_lt_rpow_of_exponent_gt he helt (by linarith)) he)
    refine ⟨i, hi, ?_⟩
    intro b t
    exact hk b t s _ hs1 hs2 hr1 hr2 hclose

private theorem exists_measurable_annular_exit_radius_real_horizon_sample {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) (T : ℝ) (hT : 0 ≤ T) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧ ∀ᵐ ω ∂P, ∀ b,
      F (b,ω) = ∫ t in (0 : ℝ)..min T (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let J : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    r^(γ^2/2) * Real.exp (γ*(H q.1 r z-H q.1 1 0 - α*Real.log (max r ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 r q.2) :=
    (hHm r hr).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) := (hHm ε hε).comp measurable_swap
  have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  let U : ContinuousPath ℂ → ℝ := fun b => min T (ContinuousPath.exitTime D b).toReal
  have hU : Measurable U := measurable_const.min ((ContinuousPath.measurable_exitTime D hD).ennreal_toReal)
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ => q.1.1 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  let S : Set ((ContinuousPath ℂ × Ω) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ U q.1.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp (measurable_fst.comp measurable_fst)))
  let Q : (ContinuousPath ℂ × Ω) × ℝ → ℝ := fun q =>
    S.indicator (fun q => J (q.1.2, q.1.1 q.2.toNNReal)) q
  have hQ : Measurable Q := by
    exact (hJ.comp ((measurable_snd.comp measurable_fst).prodMk heval)).indicator hS
  refine ⟨fun q => ∫ t, Q (q,t), hQ.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b
  have hU0 : 0 ≤ U b := le_min hT ENNReal.toReal_nonneg
  rw [intervalIntegral.integral_of_le hU0, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Q, S, U, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc, J, A]
  split_ifs with ht hz
  · rw [hω r (b t.toNNReal), hω ε (b t.toNNReal), hω 1 0,
      hrec r (b t.toNNReal) hr, hrec ε (b t.toNNReal) hε]
  · rfl
  · rfl



private theorem ae_continuous_inserted_density
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α : ℝ) :
    ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (fun z : ℂ => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec r hr
  have hcont : Continuous (hcirc ω r) := by
    rw [← funext (hω r)]
    exact hHc ω r hr
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
      fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
    funext z
    exact (hrec r z hr).symm
  have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
    rw [heq]
    exact (hcont.sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))

private theorem aemeasurable_annular_exit_radius_real_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ α δ : ℝ)
    {D : Set ℂ} (hD : IsOpen D) {T : ℝ} (hT : 0 ≤ T) :
    let A : ℝ → (Ω × ContinuousPath ℂ) → ℝ := fun v p =>
      ∫ u in (0 : ℝ)..min T (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z))
          (p.2 u.toNNReal)
    AEMeasurable (fun p => A r p - A ε p) (P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ :=
    exists_measurable_annular_exit_radius_real_horizon_sample hh hε hr γ α δ hD T hT
  apply (hFm.comp measurable_swap).aemeasurable.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hFae,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_continuous_inserted_density hh γ α)] with p hF hc
  change F (p.2, p.1) = _
  rw [hF]
  let f : ℂ → ℝ := fun z => r^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)
  let g : ℂ → ℝ := fun z => ε^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)
  have hf := intervalIntegrable_annular_density f (hc r hr) δ p.2 0
    (min T (ContinuousPath.exitTime D p.2).toReal)
  have hg := intervalIntegrable_annular_density g (hc ε hε) δ p.2 0
    (min T (ContinuousPath.exitTime D p.2).toReal)
  rw [← intervalIntegral.integral_sub hf hg]
  apply intervalIntegral.integral_congr
  intro u hu
  simp [f, g, Set.indicator_sub]


private def horizonRationalTime (N : ℕ) (q : ℚ) : Icc (0 : ℝ) N :=
  ⟨min (N : ℝ) (max (q : ℝ) 0), ⟨le_min (Nat.cast_nonneg N) (le_max_right _ _), min_le_left _ _⟩⟩

private theorem horizon_iSup_eq_rational (N : ℕ) (f : ℝ → ℝ≥0∞) (hf : Continuous f) :
    (⨆ t : Icc (0 : ℝ) N, f t) = ⨆ q : ℚ, f (horizonRationalTime N q) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hc : Continuous (fun x : ℝ => f (min N (max x 0))) :=
      hf.comp (continuous_const.min (continuous_id.max continuous_const))
    have hclosed : IsClosed {x : ℝ | f (min N (max x 0)) ≤ ⨆ q : ℚ, f (horizonRationalTime N q)} :=
      isClosed_le hc continuous_const
    have hall : ∀ x : ℝ, f (min N (max x 0)) ≤ ⨆ q : ℚ, f (horizonRationalTime N q) := by
      intro x
      refine Rat.denseRange_cast.induction_on x hclosed ?_
      intro q
      exact le_iSup (fun q : ℚ => f (horizonRationalTime N q)) q
    simpa only [max_eq_left t.property.1, min_eq_right t.property.2] using hall t
  · apply iSup_le
    intro q
    exact le_iSup (fun t : Icc (0 : ℝ) N => f t) (horizonRationalTime N q)

/-- The finite-horizon supremum of the difference of two positive-radius
exit-stopped annular clocks is product almost-everywhere measurable. -/
theorem aemeasurable_annular_exit_clock_radius_iSup
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (γ α δ : ℝ)
    {D : Set ℂ} (hD : IsOpen D) (N : ℕ) :
    let A : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      ∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z))
          (p.2 u.toNNReal)
    AEMeasurable (fun p => ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal |A r p t - A ε p t|)
      (P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  let A : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    ∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D p.2).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z))
        (p.2 u.toNNReal)
  have hq (q : ℚ) : AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |A r p (horizonRationalTime N q) - A ε p (horizonRationalTime N q)|)
      (P.prod (planarBrownianMotion x)) := by
    exact ((aemeasurable_annular_exit_radius_real_time hh x hε hr γ α δ hD
      (horizonRationalTime N q).property.1).abs).ennreal_ofReal
  apply (AEMeasurable.iSup hq).congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
    (ae_continuous_inserted_density hh γ α)] with p hc
  have htime (v : ℝ) (hv : 0 < v) : Continuous (A v p) := by
    exact (intervalIntegral.continuous_primitive
      (fun a c => intervalIntegrable_annular_density _ (hc v hv) δ p.2 a c) 0).comp
        (continuous_id.min continuous_const)
  exact (horizon_iSup_eq_rational N _
    (ENNReal.continuous_ofReal.comp ((htime r hr).sub (htime ε hε)).abs)).symm


/-- Grid-to-dyadic exit-stopped clock differences are almost surely summable
uniformly in time on every finite integer horizon. -/
theorem exists_ae_tsum_annular_grid_exit_clock_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ,
      ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)), ∀ N : ℕ,
        let A : ℝ → ℝ → ℝ := fun v t =>
          ∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D p.2).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z))
              (p.2 u.toNNReal)
        (∑' j : ℕ, ∑ i ∈ Finset.range (gridCount c (j+K) + 1),
          ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
            |A (gridScale (gridCount c) (j+K) i) t - A (dyadicScale (j+K)) t|) < ⊤ := by
  obtain ⟨c, hc, K, hK⟩ := exists_tsum_annular_grid_exit_clock_lt_top hh x hγ0 hγ2 α hδ
  refine ⟨c, hc, K, ?_⟩
  apply ae_all_iff.mpr
  intro N
  let A : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    ∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D p.2).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z))
        (p.2 u.toNNReal)
  let S : ℕ → ℕ → (Ω × ContinuousPath ℂ) → ℝ≥0∞ := fun j i p =>
    ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
      |A (gridScale (gridCount c) (j+K) i) p t - A (dyadicScale (j+K)) p t|
  have hS (j i : ℕ) (hi : i ∈ Finset.range (gridCount c (j+K) + 1)) :
      AEMeasurable (S j i) (P.prod (planarBrownianMotion x)) := by
    have hi' : i ≤ gridCount c (j+K) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hr : 0 < gridScale (gridCount c) (j+K) i :=
      (half_pos (dyadicScale_pos (j+K))).trans_le (gridScale_mem_Icc (gridCount c) hi').1
    exact aemeasurable_annular_exit_clock_radius_iSup hh x (dyadicScale_pos (j+K)) hr γ α δ hD N
  have hm (j : ℕ) : AEMeasurable (fun p => ∑ i ∈ Finset.range (gridCount c (j+K) + 1), S j i p)
      (P.prod (planarBrownianMotion x)) :=
    Finset.aemeasurable_fun_sum _ fun i hi => hS j i hi
  have hint : (∫⁻ p, ∑' j, ∑ i ∈ Finset.range (gridCount c (j+K) + 1), S j i p
      ∂(P.prod (planarBrownianMotion x))) < ⊤ := by
    rw [lintegral_tsum hm]
    simp_rw [lintegral_finsetSum' _ (fun i hi => hS _ i hi)]
    exact (hK D hDb).2 N
  exact ae_lt_top' (AEMeasurable.tsum hm) hint.ne


/-- On each finite time interval the exit-stopped annular clocks converge
uniformly over every radius in sufficiently small dyadic shells. -/
theorem ae_annular_exit_clock_shell_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D p.2 < ⊤ ∧ ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
          ∀ s : ℝ, dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
            ∀ t : ℝ≥0, t ≤ T →
              |(∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
                {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                  s^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) s z))
                  (p.2 u.toNNReal)) - F t| < ε := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨c, hc, K, hgrid⟩ :=
    exists_ae_tsum_annular_grid_exit_clock_lt_top hh x hγ0 hγ2 α hδ hD hDb
  obtain ⟨η, hη, hmod⟩ := ae_eventually_annular_exit_clock_grid_comparison hh α γ hδ hc D
  filter_upwards [hgrid,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hmod,
    ae_exists_locally_uniform_limit_annularClock_stopped hh x hγ0 hγ2 α hδ hDb]
    with ⟨ω, b⟩ hgridb hmodω hdyadb
  obtain ⟨hfin, F, hFc, hF0, hFm, hF⟩ := hdyadb
  refine ⟨hfin, F, hFc, hF0, hFm, ?_⟩
  intro T ε hε
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  let A : ℝ → ℝ → ℝ := fun v t =>
    ∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z))
        (b u.toNNReal)
  let S : ℕ → ℝ≥0∞ := fun j => ∑ i ∈ Finset.range (gridCount c (j+K) + 1),
    ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
      |A (gridScale (gridCount c) (j+K) i) t - A (dyadicScale (j+K)) t|
  have hsum : (∑' j, S j) < ⊤ := hgridb N
  have hfinite : ∀ j, S j ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top hsum.ne
  have hS : Tendsto (fun j => (S j).toReal) atTop (𝓝 0) :=
    (ENNReal.tendsto_toReal_zero_iff hfinite).2 (ENNReal.tendsto_atTop_zero_of_tsum_ne_top hsum.ne)
  have hM : 0 < F T + 2 := by linarith [hF0 T]
  let a : ℝ := min 1 (ε / 4)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hηsmall : ∀ᶠ k in atTop, |η k| < ε / (4 * (F T + 2)) := by
    have hhη := hη.abs.eventually (Iio_mem_nhds (show |(0 : ℝ)| < ε / (4 * (F T + 2)) by simpa using (show 0 < ε / (4 * (F T + 2)) by positivity)))
    simpa using hhη
  have hsmallS := hS.eventually (Iio_mem_nhds ha)
  have hsmallF := hF T a ha
  have hshift : Tendsto (fun j : ℕ => j + K) atTop atTop := tendsto_add_atTop_nat K
  have hfinal : ∀ᶠ j in atTop, ∀ s : ℝ,
      dyadicScale (j+K) / 2 ≤ s → s ≤ dyadicScale (j+K) →
      ∀ t : ℝ≥0, t ≤ T → |A s t - F t| < ε := by
    filter_upwards [hshift.eventually hmodω, hshift.eventually hηsmall, hsmallS,
      hshift.eventually hsmallF] with j hjmod hjη hjS hjF s hs1 hs2 t ht
    obtain ⟨i, hi, hiComp⟩ := hjmod s hs1 hs2
    let r := gridScale (gridCount c) (j+K) i
    let u : Icc (0 : ℝ) N := ⟨t, ⟨t.coe_nonneg, le_trans (show (t : ℝ) ≤ T from ht) hN⟩⟩
    have hle : ENNReal.ofReal |A r t - A (dyadicScale (j+K)) t| ≤ S j := by
      have ht' := le_iSup (fun u : Icc (0 : ℝ) N => ENNReal.ofReal
        |A r u - A (dyadicScale (j+K)) u|) u
      apply ht'.trans
      dsimp only [S, r]
      exact Finset.single_le_sum (f := fun i : ℕ =>
        ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
          |A (gridScale (gridCount c) (j+K) i) t - A (dyadicScale (j+K)) t|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    have hdiff : |A r t - A (dyadicScale (j+K)) t| < a := by
      have h := ENNReal.toReal_mono (hfinite j) hle
      rw [ENNReal.toReal_ofReal (abs_nonneg _)] at h
      exact h.trans_lt hjS
    have hdyad : |A (dyadicScale (j+K)) t - F t| < a := hjF t ht
    have har : |A r t| < F T + 2 := by
      have hab := abs_add_le (A r t - A (dyadicScale (j+K)) t)
        (A (dyadicScale (j+K)) t - F t + F t)
      have hab' := abs_add_le (A (dyadicScale (j+K)) t - F t) (F t)
      have hft : |F t| ≤ F T := by rw [abs_of_nonneg (hF0 t)]; exact hFm ht
      have ha1 : a ≤ 1 := min_le_left _ _
      have heq : A r t = (A r t - A (dyadicScale (j+K)) t) +
          (A (dyadicScale (j+K)) t - F t + F t) := by ring
      rw [heq]
      linarith
    have hcomp : |A s t - A r t| ≤ η (j+K) * A r t := hiComp b t
    have heta : η (j+K) * A r t < ε / 4 := by
      calc
        _ ≤ |η (j+K)| * |A r t| := by rw [← abs_mul]; exact le_abs_self _
        _ ≤ |η (j+K)| * (F T + 2) := mul_le_mul_of_nonneg_left har.le (abs_nonneg _)
        _ < (ε / (4 * (F T + 2))) * (F T + 2) :=
          mul_lt_mul_of_pos_right hjη hM
        _ = ε / 4 := by field_simp
    have htriangle := abs_add_le (A s t - A r t) (A r t - A (dyadicScale (j+K)) t)
    have htriangle' := abs_add_le (A s t - A (dyadicScale (j+K)) t)
      (A (dyadicScale (j+K)) t - F t)
    have heq : A s t - F t = (A s t - A (dyadicScale (j+K)) t) +
        (A (dyadicScale (j+K)) t - F t) := by ring
    have haε : a ≤ ε / 4 := min_le_right _ _
    rw [heq]
    have heq' : A s t - A (dyadicScale (j+K)) t =
        (A s t - A r t) + (A r t - A (dyadicScale (j+K)) t) := by ring
    rw [heq'] at htriangle' ⊢
    linarith
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hfinal
  refine eventually_atTop.mpr ⟨J+K, ?_⟩
  intro k hk s hs1 hs2 t ht
  have hkK : K ≤ k := by omega
  have hkJ : J ≤ k-K := by omega
  have hhJ := hJ (k-K) hkJ
  rw [Nat.sub_add_cancel hkK] at hhJ
  exact hhJ s hs1 hs2 t ht


/-- For a fixed Brownian starting point, the actual exit-stopped annular clocks
converge uniformly on every finite time interval as the positive smoothing
radius tends to zero. -/
theorem ae_annular_exit_clock_continuum_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D p.2 < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ s : ℝ, 0 < s → s < ρ → ∀ t : ℝ≥0, t ≤ T →
            |(∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                s^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) s z))
                (p.2 u.toNNReal)) - F t| < ε := by
  filter_upwards [ae_annular_exit_clock_shell_convergence hh x hγ0 hγ2 α hδ hD hDb]
    with p hp
  obtain ⟨hfin, F, hFc, hF0, hFm, hF⟩ := hp
  refine ⟨hfin, F, hFc, hF0, hFm, ?_⟩
  intro T ε hε
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hF T ε hε)
  refine ⟨dyadicScale K, dyadicScale_pos K, ?_⟩
  intro s hs hsmall t ht
  obtain ⟨k, hk1, hk2⟩ := exists_dyadicScale_bracket hs
    (hsmall.trans_le (dyadicScale_le_one' K))
  change s < LatticeProb.LQG.dyadicScale K at hsmall
  have hKk : K ≤ k := by
    by_contra hn
    have hle := dyadicScale_le_of_le (show k + 1 ≤ K by omega)
    linarith
  apply hK k hKk s _ hk2.le t ht
  change LatticeProb.LQG.dyadicScale k / 2 ≤ s
  simpa only [dyadicScale_succ_eq_half] using hk1

/-- Field-then-path form of the locally uniform continuum-radius limit. -/
theorem ae_field_ae_path_annular_exit_clock_continuum_convergence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousPath.exitTime D b < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ s : ℝ, 0 < s → s < ρ → ∀ t : ℝ≥0, t ≤ T →
            |(∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                s^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z))
                (b u.toNNReal)) - F t| < ε := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  exact Measure.ae_ae_of_ae_prod
    (ae_annular_exit_clock_continuum_convergence hh x hγ0 hγ2 α hδ hD hDb)

end HarmonicBalls
