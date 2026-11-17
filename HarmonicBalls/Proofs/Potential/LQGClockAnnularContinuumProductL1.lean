import HarmonicBalls.Proofs.Potential.LQGClockAnnularContinuumUniformL1
import HarmonicBalls.Proofs.Potential.LQGClockAnnularCellSecondMoment

/-! # Product moments of annular clocks

The stopped annular clocks have a uniform product second-moment bound on
finite time intervals.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Topology

namespace HarmonicBalls

/-- A nonnegative annular clock stopped before a fixed horizon is bounded by
its unstopped nonnegative occupation integral. -/
theorem ofReal_stopped_annular_clock_le_lintegral (f : ℂ → ℝ) (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (δ : ℝ) (b : ContinuousPath ℂ) {T τ : ℝ}
    (hT : 0 ≤ T) (hτ : 0 ≤ τ) :
    ENNReal.ofReal (∫ s in (0 : ℝ)..min T τ,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) ≤
      ∫⁻ s in Ioc 0 T, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  let g : ℝ → ℝ := fun s =>
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)
  have hg0 (s : ℝ) : 0 ≤ g s := by
    simp only [g, Set.indicator_apply]
    split_ifs
    · exact hf0 _
    · exact le_rfl
  have hmin : 0 ≤ min T τ := le_min hT hτ
  have hi := intervalIntegrable_annular_density f hf δ b 0 (min T τ)
  change ENNReal.ofReal (∫ s in (0 : ℝ)..min T τ, g s) ≤ ∫⁻ s in Ioc 0 T, ENNReal.ofReal (g s)
  rw [intervalIntegral.integral_of_le hmin,
    ofReal_integral_eq_lintegral_ofReal hi.1 (Filter.Eventually.of_forall hg0)]
  exact lintegral_mono_set (Ioc_subset_Ioc_right (min_le_left _ _))

/-- The square of the stopped annular clock has a uniform integral bound over the
field and Brownian path as the positive smoothing radius tends to zero. -/
theorem exists_lintegral_prod_stopped_annular_clock_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ)
    (D : Set ℂ) {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ δ →
      (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal (∫ s in (0 : ℝ)..
        min T (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
          (p.2 s.toNNReal)) ^ 2 ∂(P.prod (planarBrownianMotion x))) ≤ C := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_annular_inserted_cell_sq_le hh x hγ hγ2 α δ
  refine ⟨C * (ENNReal.ofReal T) ^ (2 - γ ^ 2 / 2), ?_, ?_⟩
  · exact ENNReal.mul_lt_top hC (ENNReal.rpow_lt_top_of_nonneg (by nlinarith) ENNReal.ofReal_ne_top)
  intro ε hε hεδ
  have hcont : ∀ᵐ ω ∂P, Continuous (fun z : ℂ => ε ^ (γ ^ 2 / 2) * Real.exp
      (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) := by
    obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    have hc : Continuous (hcirc ω ε) := by
      rw [← funext (hω ε)]
      exact hHc ω ε hε
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) =
        fun z => hcirc ω ε z - hcirc ω 1 0 - α * Real.log (max ε ‖z‖) := by
      funext z
      exact (hrec ε z hε).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  have hp : ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      Continuous (fun z : ℂ => ε ^ (γ ^ 2 / 2) * Real.exp
        (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) :=
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hcont
  calc
    _ ≤ ∫⁻ p : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc (0 : ℝ) T, ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
          (p.2 s.toNNReal))) ^ 2 ∂(P.prod (planarBrownianMotion x)) := by
      apply lintegral_mono_ae
      filter_upwards [hp] with p hc
      gcongr
      exact ofReal_stopped_annular_clock_le_lintegral _ hc
        (fun z => mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le)
        δ p.2 hT.le ENNReal.toReal_nonneg
    _ ≤ _ := by simpa using hbound hε hεδ 0 T le_rfl hT


/-- For each positive smoothing radius, the actual exit-stopped annular clock
at a fixed time is measurable for the product law. -/
theorem aemeasurable_stopped_annular_clock_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {ε : ℝ} (hε : 0 < ε) (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D)
    {T : ℝ} (hT : 0 ≤ T) :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      ∫ t in (0 : ℝ)..min T (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
            (p.2 t.toNNReal)) (P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let J : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp
  let U : ContinuousPath ℂ → ℝ := fun b => min T (ContinuousPath.exitTime D b).toReal
  have hU : Measurable U := measurable_const.min ((ContinuousPath.measurable_exitTime D hD).ennreal_toReal)
  have heval : Measurable (fun q : (Ω × ContinuousPath ℂ) × ℝ => q.1.2 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))
  let S : Set ((Ω × ContinuousPath ℂ) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ U q.1.2}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp (measurable_snd.comp measurable_fst)))
  let Q : (Ω × ContinuousPath ℂ) × ℝ → ℝ := fun q =>
    S.indicator (fun q => J (q.1.1, q.1.2 q.2.toNNReal)) q
  have hQ : Measurable Q := by
    exact (hJ.comp ((measurable_fst.comp measurable_fst).prodMk heval)).indicator hS
  let F : Ω × ContinuousPath ℂ → ℝ := fun p => ∫ t, Q (p,t)
  have hF : Measurable F := hQ.stronglyMeasurable.integral_prod_right'.measurable
  apply hF.aemeasurable.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hHae,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_recentered_inserted_circle_average hh α)] with p hω hrec
  have hU0 : 0 ≤ U p.2 := le_min hT ENNReal.toReal_nonneg
  rw [intervalIntegral.integral_of_le hU0, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Q, S, U, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc, J, A]
  split_ifs with ht hz
  · rw [hω ε (p.2 t.toNNReal), hω 1 0, hrec ε (p.2 t.toNNReal) hε]
  · rfl
  · rfl


private theorem uniformIntegrable_of_eLpNorm_two_le
    {X ι : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
    (F : ι → X → ℝ) (hF : ∀ i, AEStronglyMeasurable (F i) μ)
    (C : ℝ≥0) (hC : ∀ i, eLpNorm (F i) 2 μ ≤ C) :
    UniformIntegrable F 1 μ := by
  have hbound (i : ι) (s : Set X) (hs : MeasurableSet s) :
      eLpNorm (F i) 1 (μ.restrict s) ≤ (C : ℝ≥0∞) * (μ s) ^ (1 / 2 : ℝ) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2)
      (by norm_num) ((hF i).restrict (s := s))
    simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat, one_div, inv_one,
      show (1 : ℝ) - (2 : ℝ)⁻¹ = 1 / 2 by norm_num, Measure.restrict_apply_univ] at h
    have h2 : eLpNorm (F i) 1 (μ.restrict s) ≤
        eLpNorm (F i) 2 (μ.restrict s) * (μ s) ^ (1 / 2 : ℝ) := by
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

/-- The finite-horizon exit-stopped annular clocks are uniformly integrable
under the joint field and Brownian law over all radii below the cutoff. -/
theorem uniformIntegrable_stopped_annular_clock_prod
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ)
    {D : Set ℂ} (hD : IsOpen D) {T : ℝ} (hT : 0 < T) :
    UniformIntegrable (fun ε : Set.Ioc (0 : ℝ) δ => fun p : Ω × ContinuousPath ℂ =>
      ∫ t in (0 : ℝ)..min T (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε : ℝ) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
            (p.2 t.toNNReal)) 1 (P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := P.prod (planarBrownianMotion x)
  let F : Set.Ioc (0 : ℝ) δ → Ω × ContinuousPath ℂ → ℝ := fun ε p =>
    ∫ t in (0 : ℝ)..min T (ContinuousPath.exitTime D p.2).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε : ℝ) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 t.toNNReal)
  have hF (ε : Set.Ioc (0 : ℝ) δ) : AEStronglyMeasurable (F ε) μ :=
    (aemeasurable_stopped_annular_clock_prod hh x ε.property.1 γ α δ hD hT.le).aestronglyMeasurable
  have hF0 (ε : Set.Ioc (0 : ℝ) δ) (p : Ω × ContinuousPath ℂ) : 0 ≤ F ε p := by
    apply intervalIntegral.integral_nonneg_of_forall (le_min hT.le ENNReal.toReal_nonneg)
    intro t
    simp only [Set.indicator_apply]
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg ε.property.1.le _) (Real.exp_pos _).le
    · exact le_rfl
  obtain ⟨C, hC, hbound⟩ := exists_lintegral_prod_stopped_annular_clock_sq_le hh x hγ hγ2 α δ D hT
  have hB : C ^ (1 / 2 : ℝ) < ∞ := ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne
  apply uniformIntegrable_of_eLpNorm_two_le F hF (C ^ (1 / 2 : ℝ)).toNNReal
  intro ε
  rw [ENNReal.coe_toNNReal hB.ne]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) (hF ε)]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  apply ENNReal.rpow_le_rpow _ (by norm_num)
  have heq : (fun p => ‖F ε p‖ₑ ^ 2) = fun p => ENNReal.ofReal (F ε p) ^ 2 := by
    funext p
    rw [Real.enorm_eq_ofReal (hF0 ε p)]
  rw [heq]
  exact hbound ε.property.1 ε.property.2

/-- A positive-radius exit-stopped annular clock has a jointly measurable
field, path and time version with continuous time paths. -/
theorem exists_measurable_stopped_annular_clock_prod_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) :
    ∃ M : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable M ∧
      (∀ p, Continuous (fun t => M (p, t))) ∧
      ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (t : ℝ≥0),
        M ((ω, b), t) = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) (b s.toNNReal) := by
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let f (ω : Ω) (z : ℂ) : ℝ := ε^(γ^2/2) * Real.exp
    (γ * (H ω ε z - H ω 1 0 - α * Real.log (max ε ‖z‖)))
  have hf (ω : Ω) : Continuous (f ω) := by
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (((hHc ω ε hε).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne'))))))
  let J : Ω × ℂ → ℝ := fun q => A.indicator (f q.1) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp
  let U : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ := fun q =>
    min (q.2 : ℝ) (ContinuousPath.exitTime D q.1.2).toReal
  have hU : Measurable U := measurable_subtype_coe.comp measurable_snd |>.min
    (((ContinuousPath.measurable_exitTime D hD).ennreal_toReal).comp
      (measurable_snd.comp measurable_fst))
  have heval : Measurable (fun q : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
      q.1.1.2 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk
        (measurable_snd.comp (measurable_fst.comp measurable_fst)))
  let S : Set (((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ U q.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp measurable_fst))
  let Q : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ → ℝ := fun q =>
    S.indicator (fun q => J (q.1.1.1, q.1.1.2 q.2.toNNReal)) q
  have hQ : Measurable Q :=
    (hJ.comp ((measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk heval)).indicator hS
  let M : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ := fun q => ∫ s, Q (q, s)
  have hM : Measurable M := hQ.stronglyMeasurable.integral_prod_right'.measurable
  have hMeq (ω : Ω) (b : ContinuousPath ℂ) (t : ℝ≥0) :
      M ((ω,b),t) = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
        A.indicator (f ω) (b s.toNNReal) := by
    have ht : (0 : ℝ) ≤ min (t : ℝ) (ContinuousPath.exitTime D b).toReal :=
      le_min t.property ENNReal.toReal_nonneg
    rw [intervalIntegral.integral_of_le ht, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with s
    simp only [Q, S, U, J, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc]
  refine ⟨M, hM, ?_, ?_⟩
  · intro p
    have heq : (fun t => M (p,t)) = fun t : ℝ≥0 =>
        ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
          A.indicator (f p.1) (p.2 s.toNNReal) := funext (hMeq p.1 p.2)
    rw [heq]
    exact (intervalIntegral.continuous_primitive
      (fun a c => intervalIntegrable_annular_density (f p.1) (hf p.1) δ p.2 a c) 0).comp
        (continuous_subtype_val.min continuous_const)
  · filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    intro b t
    rw [hMeq]
    apply intervalIntegral.integral_congr
    intro s hs
    simp only [A, Set.indicator_apply]
    split_ifs with hz
    · simp only [f, hω ε (b s.toNNReal), hω 1 0, hrec ε (b s.toNNReal) hε]
    · rfl

/-- The continuum limit of the actual exit-stopped annular clocks has a jointly
measurable field, path and time representative. -/
theorem exists_measurable_annular_exit_clock_continuum_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable F ∧
      (∀ p, Continuous (fun t => F (p,t)) ∧ (∀ t, 0 ≤ F (p,t)) ∧
        Monotone (fun t => F (p,t))) ∧
      ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ r : ℝ, 0 < r → r < ρ → ∀ t : ℝ≥0, t ≤ T →
            |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                  (hcirc p.1) r z)) (p.2 s.toNNReal)) - F (p,t)| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := P.prod (planarBrownianMotion x)
  choose M hMm hMc hMae using fun k : ℕ =>
    exists_measurable_stopped_annular_clock_prod_time hh (dyadicScale_pos k) γ α δ hD
  have hM : ∀ᵐ p : Ω × ContinuousPath ℂ ∂μ, ∀ k t,
      M k (p,t) = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (dyadicScale k)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
            (hcirc p.1) (dyadicScale k) z)) (p.2 s.toNNReal) := by
    have h := (ae_all_iff.mpr hMae)
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae h] with p hp k t
    exact hp k p.2 t
  have hconv := ae_annular_exit_clock_continuum_convergence hh x hγ hγ2 α hδ hD hDb
  have hseq : ∀ᵐ p ∂μ, ∃ G : ℝ≥0 → ℝ,
      Continuous G ∧ (∀ t, 0 ≤ G t) ∧ Monotone G ∧
      ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ t : ℝ≥0, t ≤ T →
        |M k (p,t) - G t| < η := by
    filter_upwards [hconv, hM] with p hp hpM
    obtain ⟨_, G, hGc, hG0, hGm, hG⟩ := hp
    refine ⟨G, hGc, hG0, hGm, ?_⟩
    intro T η hη
    obtain ⟨ρ, hρ, hρbound⟩ := hG T η hη
    have hs : ∀ᶠ k in atTop, dyadicScale k < ρ :=
      LatticeProb.LQG.LQGSingularScaledLimit.tendsto_dyadicScale_zero.eventually (Iio_mem_nhds hρ)
    filter_upwards [hs] with k hk t ht
    rw [hpM k t]
    exact hρbound _ (dyadicScale_pos k) hk t ht
  obtain ⟨F, hFm, hFr, hFseq⟩ := exists_measurable_locally_uniform_limit μ M hMm hseq
  refine ⟨F, hFm, hFr, ?_⟩
  filter_upwards [hconv, hM, hFseq] with p hp hpM hpF
  obtain ⟨_, G, hGc, hG0, hGm, hG⟩ := hp
  have heq (t : ℝ≥0) : G t = F (p,t) := by
    have hgt : Tendsto (fun k => M k (p,t)) atTop (𝓝 (G t)) := by
      apply Metric.tendsto_nhds.mpr
      intro η hη
      obtain ⟨ρ, hρ, hρbound⟩ := hG t η hη
      have hs : ∀ᶠ k in atTop, dyadicScale k < ρ :=
        LatticeProb.LQG.LQGSingularScaledLimit.tendsto_dyadicScale_zero.eventually (Iio_mem_nhds hρ)
      filter_upwards [hs] with k hk
      rw [Real.dist_eq, hpM k t]
      exact hρbound _ (dyadicScale_pos k) hk t le_rfl
    have hft : Tendsto (fun k => M k (p,t)) atTop (𝓝 (F (p,t))) := by
      apply Metric.tendsto_nhds.mpr
      intro η hη
      filter_upwards [hpF t η hη] with k hk
      simpa only [Real.dist_eq] using hk t le_rfl
    exact tendsto_nhds_unique hgt hft
  intro T η hη
  obtain ⟨ρ, hρ, hρbound⟩ := hG T η hη
  refine ⟨ρ, hρ, ?_⟩
  intro r hr hrρ t ht
  rw [← heq t]
  exact hρbound r hr hrρ t ht

end HarmonicBalls
