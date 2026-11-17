import HarmonicBalls.Proofs.Potential.LQGClockAnnularContinuumUniformL1
import HarmonicBalls.Proofs.Potential.LQGClockAnnularCellSecondMoment

/-! # Product convergence of annular clocks

The exit-stopped annular clocks have uniformly bounded product second moments
and converge in uniform-time product L¹ on finite time intervals.
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

/-- Uniformly integrable scalar bounds upgrade almost-everywhere convergence
of Banach-valued functions to convergence of their expected distances. -/
private theorem integral_norm_sub_tendsto_of_uniformIntegrable_bound
    {X E : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℕ → X → E) (hA : ∀ n, AEStronglyMeasurable (A n) μ)
    (B : X → E) (H : ℕ → X → ℝ) (hH : UniformIntegrable H 1 μ)
    (hbound : ∀ n, ∀ᵐ x ∂μ, ‖A n x‖ ≤ ‖H n x‖)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun n => A n x) atTop (𝓝 (B x))) :
    (∀ n, Integrable (fun x => ‖A n x - B x‖) μ) ∧
      Tendsto (fun n => ∫ x, ‖A n x - B x‖ ∂μ) atTop (𝓝 0) := by
  have hb (n : ℕ) : (‖A n ·‖ₑ) ≤ᵐ[μ] (‖H n ·‖ₑ) := by
    filter_upwards [hbound n] with x hx
    exact enorm_le_iff_norm_le.mpr hx
  have hAu : UniformIntegrable A 1 μ := by
    refine ⟨unifIntegrable_iff.mpr ?_, ?_⟩
    · intro ε hε
      obtain ⟨δ, hδ, hδb⟩ := unifIntegrable_iff.mp hH.1 ε hε
      refine ⟨δ, hδ, fun n s hs => ?_⟩
      exact (eLpNorm_mono_enorm_ae (hA n).restrict
        ((hb n).filter_mono ae_restrict_le)).trans (hδb n s hs)
    · obtain ⟨C, hC⟩ := hH.2
      exact ⟨C, fun n => (eLpNorm_mono_enorm_ae (hA n) (hb n)).trans (hC n)⟩
  have hB : MemLp B 1 μ := hAu.memLp_of_ae_tendsto hconv
  have hAi (n : ℕ) : Integrable (A n - B) μ :=
    memLp_one_iff_integrable.mp ((hAu.memLp n).sub hB)
  have hLp := tendsto_Lp_finite_of_tendsto_ae (p := 1) le_rfl (by norm_num)
    hA hB hAu.unifIntegrable hconv
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLp
  have heq (n : ℕ) : (eLpNorm (A n - B) 1 μ).toReal =
      ∫ x, ‖A n x - B x‖ ∂μ := by
    rw [eLpNorm_one_eq_lintegral_enorm (hAi n).aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm (hAi n),
      ENNReal.toReal_ofReal (integral_nonneg (fun x : X => norm_nonneg ((A n - B) x)))]
    rfl
  refine ⟨fun n => (hAi n).norm, ?_⟩
  simpa only [Function.comp_def, heq, ENNReal.toReal_zero] using hreal

/-- A nonnegative continuous annular density gives a stopped clock bounded
by its value at any later nonnegative time. -/
private theorem stopped_annular_clock_le_at_horizon (f : ℂ → ℝ) (hf : Continuous f)
    (hf0 : ∀ z, 0 ≤ f z) (δ : ℝ) (b : ContinuousPath ℂ) (D : Set ℂ)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    |∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)| ≤
    ∫ s in (0 : ℝ)..min T (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal) := by
  let g : ℝ → ℝ := fun s =>
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)
  have hg0 (s : ℝ) : 0 ≤ g s := by
    simp only [g, Set.indicator_apply]
    split_ifs
    · exact hf0 _
    · exact le_rfl
  have hmin : 0 ≤ min t (ContinuousPath.exitTime D b).toReal :=
    le_min ht ENNReal.toReal_nonneg
  have hminT : min t (ContinuousPath.exitTime D b).toReal ≤
      min T (ContinuousPath.exitTime D b).toReal := min_le_min_right _ htT
  change |∫ s in (0 : ℝ)..min t (ContinuousPath.exitTime D b).toReal, g s| ≤
    ∫ s in (0 : ℝ)..min T (ContinuousPath.exitTime D b).toReal, g s
  rw [abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hmin hg0)]
  exact intervalIntegral.integral_mono_interval le_rfl hmin hminT
    (Filter.Eventually.of_forall hg0)
    (intervalIntegrable_annular_density f hf δ b 0 _)

/-- Along any positive radii bounded by the cutoff and tending to zero, the
actual exit-stopped clocks converge in product-law uniform-time L¹. -/
theorem exists_measurable_annular_exit_clock_sequence_uniformL1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable F ∧
      (∀ p, Continuous (fun t => F (p,t)) ∧ (∀ t, 0 ≤ F (p,t)) ∧
        Monotone (fun t => F (p,t))) ∧
      (∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ r : ℝ, 0 < r → r < ρ → ∀ t : ℝ≥0, t ≤ T →
            |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                  (hcirc p.1) r z)) (p.2 s.toNNReal)) - F (p,t)| < η) ∧
      ∀ T : ℝ≥0, 0 < T → ∀ r : ℕ → Set.Ioc (0 : ℝ) δ,
        Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0) →
        ∃ (A : ℕ → Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ))
          (B : Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ)),
          (∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ n t,
            A n p t = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                (r n : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                  (hcirc p.1) (r n) z)) (p.2 s.toNNReal)) ∧
          (∀ p t, B p t = F (p, (t : ℝ).toNNReal)) ∧
          Measurable B ∧
          (∀ n, Integrable (fun p => ‖A n p - B p‖) (P.prod (planarBrownianMotion x))) ∧
          Tendsto (fun n => ∫ p, ‖A n p - B p‖ ∂(P.prod (planarBrownianMotion x)))
            atTop (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := P.prod (planarBrownianMotion x)
  obtain ⟨F, hFm, hFr, hFlim⟩ :=
    exists_measurable_annular_exit_clock_continuum_limit hh x hγ hγ2 α hδ hD hDb
  refine ⟨F, hFm, hFr, hFlim, ?_⟩
  intro T hT r hr
  choose M hMm hMc hMae using fun n : ℕ =>
    exists_measurable_stopped_annular_clock_prod_time hh (r n).property.1 γ α δ hD
  let A : ℕ → Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun n p =>
    ⟨fun t => M n (p, (t : ℝ).toNNReal),
      (hMc n p).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  let B : Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun p =>
    ⟨fun t => F (p, (t : ℝ).toNNReal),
      (hFr p).1.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hAm (n : ℕ) : Measurable (A n) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm n).comp (measurable_id.prodMk measurable_const)
  have hBm : Measurable B := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hFm.comp (measurable_id.prodMk measurable_const)
  have hM : ∀ᵐ p : Ω × ContinuousPath ℂ ∂μ, ∀ n t,
      M n (p,t) = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (r n : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
            (hcirc p.1) (r n) z)) (p.2 s.toNNReal) := by
    have h := ae_all_iff.mpr hMae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae h] with p hp n t
    exact hp n p.2 t
  have hAeq : ∀ᵐ p ∂μ, ∀ n t,
      A n p t = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (r n : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
            (hcirc p.1) (r n) z)) (p.2 s.toNNReal) := by
    filter_upwards [hM] with p hp n t
    simpa only [A, ContinuousMap.coe_mk, Real.toNNReal_of_nonneg t.property.1,
      NNReal.coe_mk] using hp n ((t : ℝ).toNNReal)
  let H : ℕ → Ω × ContinuousPath ℂ → ℝ := fun n p =>
    ∫ s in (0 : ℝ)..min (T : ℝ) (ContinuousPath.exitTime D p.2).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (r n : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
          (hcirc p.1) (r n) z)) (p.2 s.toNNReal)
  have hTu : (0 : ℝ) < T := by exact_mod_cast hT
  have hHu : UniformIntegrable H 1 μ := by
    have hU := uniformIntegrable_stopped_annular_clock_prod hh x hγ.ne' hγ2 α δ hD hTu
    refine ⟨hU.1.comp r, ?_⟩
    obtain ⟨C, hC⟩ := hU.2
    exact ⟨C, fun n => hC (r n)⟩
  have hcont (n : ℕ) : ∀ᵐ ω ∂P, Continuous (fun z : ℂ =>
      (r n : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
        (hcirc ω) (r n) z)) := by
    filter_upwards [hh.ae_continuous_circle_fixed (r n).property.1,
      ae_recentered_inserted_circle_average hh α] with ω hc hrec
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (r n) z) =
        fun z => hcirc ω (r n) z - hcirc ω 1 0 - α * Real.log (max (r n : ℝ) ‖z‖) := by
      funext z
      exact (hrec _ z (r n).property.1).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (r n) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (r n).property.1).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  have hbound (n : ℕ) : ∀ᵐ p ∂μ, ‖A n p‖ ≤ ‖H n p‖ := by
    filter_upwards [hAeq, (Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae (hcont n)] with p hp hc
    have hH0 : 0 ≤ H n p := by
      apply intervalIntegral.integral_nonneg_of_forall (le_min hTu.le ENNReal.toReal_nonneg)
      intro s
      simp only [Set.indicator_apply]
      split_ifs
      · exact mul_nonneg (Real.rpow_nonneg (r n).property.1.le _) (Real.exp_pos _).le
      · exact le_rfl
    rw [Real.norm_eq_abs, abs_of_nonneg hH0]
    apply (ContinuousMap.norm_le (A n p) hH0).2
    intro t
    rw [Real.norm_eq_abs, hp n t]
    exact stopped_annular_clock_le_at_horizon _ hc
      (fun z => mul_nonneg (Real.rpow_nonneg (r n).property.1.le _) (Real.exp_pos _).le)
      δ p.2 D t.property.1 t.property.2
  have hconv : ∀ᵐ p ∂μ, Tendsto (fun n => A n p) atTop (𝓝 (B p)) := by
    filter_upwards [hFlim, hAeq] with p hp hpa
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨ρ, hρ, hρb⟩ := hp T (η / 2) (half_pos hη)
    have hrs : ∀ᶠ n in atTop, (r n : ℝ) < ρ := hr.eventually (Iio_mem_nhds hρ)
    filter_upwards [hrs] with n hn
    have hle : ‖A n p - B p‖ ≤ η / 2 := by
      apply (ContinuousMap.norm_le (A n p - B p) (le_of_lt (half_pos hη))).2
      intro t
      have ht : (t : ℝ).toNNReal ≤ T := by
        exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
      have h := (hρb (r n) (r n).property.1 hn ((t : ℝ).toNNReal) ht).le
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs, B, ContinuousMap.coe_mk,
        hpa n t, Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using h
    rw [dist_eq_norm]
    exact lt_of_le_of_lt hle (half_lt_self hη)
  obtain ⟨hi, ht⟩ := integral_norm_sub_tendsto_of_uniformIntegrable_bound A
    (fun n => (hAm n).aestronglyMeasurable) B H hHu hbound hconv
  exact ⟨A, B, hAeq, fun _ _ => rfl, hBm, hi, ht⟩

/-- The exit-stopped annular clocks converge in product-law uniform-time L¹
as the positive smoothing radius tends to zero. -/
theorem exists_measurable_annular_exit_clock_uniformL1
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable F ∧
      (∀ p, Continuous (fun t => F (p,t)) ∧ (∀ t, 0 ≤ F (p,t)) ∧
        Monotone (fun t => F (p,t))) ∧
      (∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∃ ρ : ℝ, 0 < ρ ∧
          ∀ r : ℝ, 0 < r → r < ρ → ∀ t : ℝ≥0, t ≤ T →
            |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                  (hcirc p.1) r z)) (p.2 s.toNNReal)) - F (p,t)| < η) ∧
      ∀ T : ℝ≥0,
        ∃ (A : Set.Ioc (0 : ℝ) δ → Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ))
          (B : Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ)),
          (∀ r, ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ t,
            A r p t = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
              {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                (r : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
                  (hcirc p.1) r z)) (p.2 s.toNNReal)) ∧
          (∀ p t, B p t = F (p, (t : ℝ).toNNReal)) ∧ Measurable B ∧
          (∀ r, Measurable (A r)) ∧
          (∀ r, Integrable (fun p => ‖A r p - B p‖) (P.prod (planarBrownianMotion x))) ∧
          Tendsto (fun r => ∫ p, ‖A r p - B p‖ ∂(P.prod (planarBrownianMotion x)))
            (Filter.comap (fun r : Set.Ioc (0 : ℝ) δ => (r : ℝ)) (𝓝[>] (0 : ℝ))) (𝓝 0) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := P.prod (planarBrownianMotion x)
  obtain ⟨F, hFm, hFr, hFlim, hseq⟩ :=
    exists_measurable_annular_exit_clock_sequence_uniformL1 hh x hγ hγ2 α hδ hD hDb
  refine ⟨F, hFm, hFr, hFlim, ?_⟩
  intro T
  choose M hMm hMc hMae using fun r : Set.Ioc (0 : ℝ) δ =>
    exists_measurable_stopped_annular_clock_prod_time hh r.property.1 γ α δ hD
  let A : Set.Ioc (0 : ℝ) δ → Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun r p =>
    ⟨fun t => M r (p, (t : ℝ).toNNReal),
      (hMc r p).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  let B : Ω × ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun p =>
    ⟨fun t => F (p, (t : ℝ).toNNReal),
      (hFr p).1.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
  have hAm (r : Set.Ioc (0 : ℝ) δ) : Measurable (A r) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm r).comp (measurable_id.prodMk measurable_const)
  have hBm : Measurable B := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact hFm.comp (measurable_id.prodMk measurable_const)
  have hAeq (r : Set.Ioc (0 : ℝ) δ) : ∀ᵐ p ∂μ, ∀ t,
      A r p t = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (r : ℝ)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α
            (hcirc p.1) r z)) (p.2 s.toNNReal) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P)
      (ν := planarBrownianMotion x)).ae (hMae r)] with p hp t
    simpa only [A, ContinuousMap.coe_mk, Real.toNNReal_of_nonneg t.property.1,
      NNReal.coe_mk] using hp p.2 ((t : ℝ).toNNReal)
  by_cases hT : 0 < T
  ·
    have hAi (r : Set.Ioc (0 : ℝ) δ) : Integrable (fun p => ‖A r p - B p‖) μ := by
      let u : ℕ → Set.Ioc (0 : ℝ) δ := fun n =>
        ⟨(r : ℝ) * dyadicScale n, mul_pos r.property.1 (dyadicScale_pos n),
          (mul_le_of_le_one_right r.property.1.le (LatticeProb.LQG.dyadicScale_le_one' n)).trans r.property.2⟩
      have hu : Tendsto (fun n => (u n : ℝ)) atTop (𝓝 0) := by
        simpa only [u, HarmonicBalls.dyadicScale, LatticeProb.LQG.dyadicScale, mul_zero] using
          LatticeProb.LQG.LQGSingularScaledLimit.tendsto_dyadicScale_zero.const_mul (r : ℝ)
      obtain ⟨C, G, hC, hG, _, hCi, _⟩ := hseq T hT u hu
      have hu0 : u 0 = r := by
        apply Subtype.ext
        simp [u, HarmonicBalls.dyadicScale]
      have hBG : B = G := by
        funext p
        ext t
        exact (hG p t).symm
      have heq : (fun p => ‖A r p - B p‖) =ᵐ[μ] (fun p => ‖C 0 p - G p‖) := by
        filter_upwards [hAeq r, hC] with p hp hpc
        have hAC : A r p = C 0 p := by
          ext t
          rw [hp t, hpc 0 t, hu0]
        rw [hAC, hBG]
      exact (hCi 0).congr heq.symm
    refine ⟨A, B, hAeq, fun _ _ => rfl, hBm, hAm, hAi, ?_⟩
    apply Filter.tendsto_iff_seq_tendsto.mpr
    intro r hr
    have hr' : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0) :=
      tendsto_nhdsWithin_iff.mp (tendsto_comap_iff.mp hr) |>.1
    obtain ⟨C, G, hC, hG, _, _, hlim⟩ := hseq T hT r hr'
    have hBG : B = G := by
      funext p
      ext t
      exact (hG p t).symm
    have heq (n : ℕ) : (fun p => ‖A (r n) p - B p‖) =ᵐ[μ]
        (fun p => ‖C n p - G p‖) := by
      filter_upwards [hAeq (r n), hC] with p hp hpc
      have hAC : A (r n) p = C n p := by
        ext t
        exact (hp t).trans (hpc n t).symm
      rw [hAC, hBG]
    have heq' (n : ℕ) : (∫ p, ‖A (r n) p - B p‖ ∂μ) =
        ∫ p, ‖C n p - G p‖ ∂μ := integral_congr_ae (heq n)
    change Tendsto (fun n => ∫ p, ‖A (r n) p - B p‖ ∂μ) atTop (𝓝 0)
    rw [funext heq']
    exact hlim
  · have hT0 : T = 0 := le_antisymm (le_of_not_gt hT) zero_le
    have hF0 : ∀ᵐ p ∂μ, F (p,0) = 0 := by
      filter_upwards [hFlim] with p hp
      by_contra hne
      have hp0 : 0 < |F (p,0)| := abs_pos.mpr hne
      obtain ⟨ρ, hρ, hρb⟩ := hp 0 (|F (p,0)| / 2) (half_pos hp0)
      have h := hρb (ρ/2) (half_pos hρ) (half_lt_self hρ) 0 le_rfl
      simp only [NNReal.coe_zero, min_eq_left ENNReal.toReal_nonneg,
        intervalIntegral.integral_same, zero_sub, abs_neg] at h
      linarith
    have ht0 (t : Icc (0 : ℝ) (T : ℝ)) : (t : ℝ) = 0 := by
      have ht := t.property
      simp only [hT0, NNReal.coe_zero] at ht
      linarith [ht.1, ht.2]
    have hz (r : Set.Ioc (0 : ℝ) δ) :
        (fun p => ‖A r p - B p‖) =ᵐ[μ] (fun _ => 0) := by
      filter_upwards [hAeq r, hF0] with p hp hp0
      have ha : A r p = 0 := by
        ext t
        rw [hp t, ht0 t]
        simp only [min_eq_left ENNReal.toReal_nonneg, intervalIntegral.integral_same,
          ContinuousMap.zero_apply]
      have hb : B p = 0 := by
        ext t
        change F (p, (t : ℝ).toNNReal) = 0
        rw [ht0 t]
        simpa only [Real.toNNReal_zero] using hp0
      simp only [ha, hb, sub_self, norm_zero]
    refine ⟨A, B, hAeq, fun _ _ => rfl, hBm, hAm, ?_, ?_⟩
    · intro r
      exact (integrable_zero _ _ _).congr (hz r).symm
    · have hi (r : Set.Ioc (0 : ℝ) δ) : ∫ p, ‖A r p - B p‖ ∂μ = 0 := by
        rw [integral_congr_ae (hz r)]
        exact integral_zero _ _
      change Tendsto (fun r => ∫ p, ‖A r p - B p‖ ∂μ) _ (𝓝 0)
      rw [funext hi]
      exact tendsto_const_nhds

end HarmonicBalls
