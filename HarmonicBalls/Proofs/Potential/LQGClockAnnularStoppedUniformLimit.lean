import HarmonicBalls.Proofs.Potential.LQGClockAnnularLimitRegularity
import HarmonicBalls.Proofs.Potential.LQGClockAnnularLimitJointMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability

/-! # Stopped annular clock limits

The actual annular clocks converge locally uniformly before and after Brownian exit.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Filter HarmonicBalls.Section6
open scoped NNReal ENNReal Topology

namespace HarmonicBalls

/-- The actual annular clocks stopped at Brownian exit converge uniformly on the unit interval.
For each fixed start, the event has full field-path product measure. -/
theorem exists_ae_continuous_monotone_limit_annularClock_stopped_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    ∃ K : ℕ, ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D p.2 < ⊤ ∧
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨K, hK⟩ := exists_ae_continuous_monotone_limit_stoppedAnnularClock hh x hγ hγ2 α hδ
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z =>
      (dyadicScale k)^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
    have hc : Continuous (hcirc ω (dyadicScale k)) := by
      rw [← funext (hω (dyadicScale k))]
      exact hHc ω (dyadicScale k) (dyadicScale_pos k)
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
        fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos k)).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  refine ⟨K, ?_⟩
  filter_upwards [hK,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hdensity,
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_planarBrownian_exitTime_bounded_lt_top x hDb)] with p hp hc hfin
  obtain ⟨F, hFc, hF0, hFm, hF⟩ := hp
  let r : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
    ⟨min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
      ⟨le_min t.2.1 ENNReal.toReal_nonneg, (min_le_left _ _).trans t.2.2⟩⟩
  have hrc : Continuous r := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.min continuous_const
  have hrm : Monotone r := by
    intro s t hst
    change min (s : ℝ) _ ≤ min (t : ℝ) _
    exact min_le_min_right _ hst
  refine ⟨hfin, F ∘ r, hFc.comp hrc, (fun t => hF0 (r t)), hFm.comp hrm, ?_⟩
  intro η hη
  filter_upwards [hF η hη] with j hj t
  have heq := stoppedAnnularClock_eq_time_integral _ (hc (j+K)).measurable δ
    (fun _ => ((r t : ℝ).toNNReal)) p.2
  have hr0 : 0 ≤ (r t : ℝ) := (r t).2.1
  have hr1 : (r t : ℝ) ≤ 1 := (r t).2.2
  simp only [NNReal.coe_one, Real.coe_toNNReal', max_eq_left hr0,
    min_eq_right hr1] at heq
  change |(∫ s in (0 : ℝ)..(r t : ℝ), _) - F (r t)| < η
  rw [← heq]
  exact hj (r t)

/-- For each fixed start, the stopped unit-interval conclusion holds for almost every field
and then for almost every Brownian path. -/
theorem exists_ae_field_ae_path_continuous_monotone_limit_annularClock_stopped_unit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    ∃ K : ℕ, ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousPath.exitTime D b < ⊤ ∧
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+K)) z))
                  (b s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨K, hK⟩ :=
    exists_ae_continuous_monotone_limit_annularClock_stopped_unit hh x hγ hγ2 α hδ hDb
  exact ⟨K, Measure.ae_ae_of_ae_prod hK⟩

/-- Locally uniform limits on bounded time intervals determine one continuous,
nonnegative and nondecreasing path. -/
theorem exists_continuous_monotone_limit_of_uniform_on_nat_intervals (A : ℕ → ℝ≥0 → ℝ)
    (hc : ∀ j, Continuous (A j)) (h0 : ∀ j t, 0 ≤ A j t)
    (hm : ∀ j, Monotone (A j))
    (h : ∀ N : ℕ, ∃ G : ℝ≥0 → ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ N → |A j t - G t| < η) :
    ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
      ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T → |A j t - F t| < η := by
  classical
  let F : ℝ≥0 → ℝ := fun t => atTop.limUnder (fun j => A j t)
  have hlimN (N : ℕ) (G : ℝ≥0 → ℝ)
      (hG : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0,
        t ≤ N → |A j t - G t| < η) (t : ℝ≥0) (ht : t ≤ N) :
      Tendsto (fun j => A j t) atTop (𝓝 (G t)) := by
    apply Metric.tendsto_nhds.mpr
    intro η hη
    filter_upwards [hG η hη] with j hj
    simpa only [Real.dist_eq] using hj t ht
  have heq (N : ℕ) (G : ℝ≥0 → ℝ)
      (hG : ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0,
        t ≤ N → |A j t - G t| < η) (t : ℝ≥0) (ht : t ≤ N) : F t = G t :=
    (hlimN N G hG t ht).limUnder_eq
  have hlim (t : ℝ≥0) : Tendsto (fun j => A j t) atTop (𝓝 (F t)) := by
    obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
    have ht : t ≤ (N : ℝ≥0) := by exact_mod_cast hN.le
    obtain ⟨G, hG⟩ := h N
    rw [heq N G hG t ht]
    exact hlimN N G hG t ht
  have hunif (N : ℕ) : TendstoUniformlyOn A F atTop (Iic (N : ℝ≥0)) := by
    obtain ⟨G, hG⟩ := h N
    rw [Metric.tendstoUniformlyOn_iff]
    intro η hη
    filter_upwards [hG η hη] with j hj t ht
    rw [heq N G hG t ht, dist_comm, Real.dist_eq]
    exact hj t ht
  refine ⟨F, ?_, (fun t => ge_of_tendsto' (hlim t) (fun j => h0 j t)), ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro t
    obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
    have ht : t < (N : ℝ≥0) := by exact_mod_cast hN
    have hcont : ContinuousOn F (Iic (N : ℝ≥0)) :=
      (hunif N).continuousOn (Eventually.of_forall fun j => (hc j).continuousOn).frequently
    exact hcont.continuousAt (Iic_mem_nhds ht)
  · intro s t hst
    exact le_of_tendsto_of_tendsto' (hlim s) (hlim t) (fun j => hm j hst)
  · intro T η hη
    obtain ⟨N, hN⟩ := exists_nat_gt (T : ℝ)
    have hTN : T ≤ (N : ℝ≥0) := by exact_mod_cast hN.le
    obtain ⟨G, hG⟩ := h N
    filter_upwards [hG η hη] with j hj t ht
    rw [heq N G hG t (ht.trans hTN)]
    exact hj t (ht.trans hTN)

private theorem ae_prod_kernel_mixture {Ω Y B : Type*} [MeasurableSpace Ω] [MeasurableSpace Y] [MeasurableSpace B]
    (P : Measure Ω) [SFinite P] (ν : Measure Y) [SFinite ν]
    (κ : Kernel Y B) [IsSFiniteKernel κ] (S : Set (Ω × B)) (hS : MeasurableSet S)
    (h : ∀ y, ∀ᵐ p ∂(P.prod (κ y)), p ∈ S) :
    ∀ᵐ p ∂(P.prod (κ ∘ₘ ν)), p ∈ S := by
  simp_rw [ae_iff] at h
  rw [ae_iff]
  have hSc : MeasurableSet Sᶜ := hS.compl
  change (P.prod (κ ∘ₘ ν)) Sᶜ = 0
  rw [Measure.prod_apply hSc]
  simp_rw [Measure.bind_apply (hSc.preimage measurable_prodMk_left) (Kernel.aemeasurable κ)]
  have hf : Measurable (fun p : Ω × Y => (κ p.2) (Prod.mk p.1 ⁻¹' Sᶜ)) := by
    let κ' : Kernel (Ω × Y) B := κ.comap Prod.snd measurable_snd
    have hset : MeasurableSet {p : (Ω × Y) × B | (p.1.1, p.2) ∈ Sᶜ} :=
      hSc.preimage ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    have hh := Kernel.measurable_kernel_prodMk_left (κ := κ') hset
    convert hh using 1
    funext p
    congr 1
  rw [lintegral_lintegral_swap hf.aemeasurable]
  calc
    _ = ∫⁻ _y, (0 : ℝ≥0∞) ∂ν := by
      apply lintegral_congr
      intro y
      have hy := h y
      change (P.prod (κ y)) Sᶜ = 0 at hy
      simpa only [Measure.prod_apply hSc] using hy
    _ = 0 := lintegral_zero

/-- A measurable field-path event valid at every start remains valid after a Brownian
time shift, with the independent field left unchanged. -/
theorem ae_prod_planarBrownianMotion_shift_of_forall_ae {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (x : ℂ) (s : ℝ≥0) (S : Set (Ω × ContinuousPath ℂ)) (hS : MeasurableSet S)
    (h : ∀ y, ∀ᵐ p ∂(P.prod (planarBrownianMotion y)), p ∈ S) :
    ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), (p.1, ContinuousPath.shift s p.2) ∈ S := by
  let K := SubMarkovKernelSemigroup.IsConservative.continuousProcess
    planarHeatSemigroup isConservative_planarHeatSemigroup
  let : IsFiniteKernel (planarHeatSemigroup.kernel s) :=
    (planarHeatSemigroup.isSubMarkovKernel s).isFiniteKernel
  let ν := planarHeatSemigroup.kernel s x
  have hs : (planarBrownianMotion x).map (ContinuousPath.shift s) = K ∘ₘ ν := by
    rw [planarBrownianMotion_eq_continuousProcess]
    have hshift := congrArg (fun K => K x)
      (SubMarkovKernelSemigroup.IsFellerKernelSemigroup.continuousProcess_map_shift
        planarHeatSemigroup isConservative_planarHeatSemigroup
        isFellerKernelSemigroup_planarHeatSemigroup kolmogorovRegular_planarHeatSemigroup s)
    rw [Kernel.map_apply _ (ContinuousPath.measurable_shift_fixed s) x,
      Kernel.comp_apply] at hshift
    exact hshift
  have ha : ∀ᵐ p ∂(P.prod ((planarBrownianMotion x).map (ContinuousPath.shift s))), p ∈ S := by
    rw [hs]
    apply ae_prod_kernel_mixture P ν K S hS
    intro y
    change ∀ᵐ p ∂(P.prod (SubMarkovKernelSemigroup.IsConservative.continuousProcess
      planarHeatSemigroup isConservative_planarHeatSemigroup y)), p ∈ S
    rw [← planarBrownianMotion_eq_continuousProcess]
    exact h y
  have heq := Measure.map_prod_map P (planarBrownianMotion x) measurable_id
    (ContinuousPath.measurable_shift_fixed s)
  rw [Measure.map_id] at heq
  rw [heq] at ha
  exact (ae_map_iff (measurable_fst.prodMk ((ContinuousPath.measurable_shift_fixed s).comp measurable_snd)).aemeasurable hS).mp ha

/-- For each start and deterministic shift, the actual annular clocks along the shifted
Brownian path converge uniformly on the unit interval under the joint law. -/
theorem ae_exists_uniform_limit_shift_stoppedAnnularClock {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) (s : ℝ≥0) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |stoppedAnnularClock (fun z => (dyadicScale j)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z)) δ
              (fun _ => ((t : ℝ).toNNReal)) (ContinuousPath.shift s p.2) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨M, hMm, hMc, hMae⟩ := exists_measurable_stoppedAnnularClock_time hh γ α δ
  let A (j : ℕ) (p : Ω × ContinuousPath ℂ) : C(Icc (0 : ℝ) 1, ℝ) :=
    ⟨fun t => M j (p, t), hMc j p⟩
  have hAm (j : ℕ) : Measurable (A j) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    exact (hMm j).comp (measurable_id.prodMk measurable_const)
  let S : Set (Ω × ContinuousPath ℂ) := {p | ∃ F, Tendsto (fun j => A j p) atTop (𝓝 F)}
  have hSm : MeasurableSet S := measurableSet_exists_tendsto hAm
  have hS (y : ℂ) : ∀ᵐ p ∂(P.prod (planarBrownianMotion y)), p ∈ S := by
    obtain ⟨K, hK⟩ := exists_ae_continuous_monotone_limit_stoppedAnnularClock hh y hγ hγ2 α hδ
    filter_upwards [hK, (Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion y)).ae hMae] with p hp hM
    obtain ⟨F, hFc, _, _, hF⟩ := hp
    let G : C(Icc (0 : ℝ) 1, ℝ) := ⟨F, hFc⟩
    refine ⟨G, (tendsto_add_atTop_iff_nat K).mp ?_⟩
    apply ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    rw [Metric.tendstoUniformly_iff]
    intro η hη
    filter_upwards [hF η hη] with j hj t
    change dist (F t) (M (j+K) (p, t)) < η
    rw [hM (j+K) p.2 t, dist_comm, Real.dist_eq]
    exact hj t
  have hshift := ae_prod_planarBrownianMotion_shift_of_forall_ae P x s S hSm hS
  filter_upwards [hshift, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hMae] with p hp hM
  obtain ⟨F, hF⟩ := hp
  refine ⟨F, F.continuous, ?_⟩
  have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp hF
  rw [Metric.tendstoUniformly_iff] at hu
  intro η hη
  filter_upwards [hu η hη] with j hj t
  have heq := hM j (ContinuousPath.shift s p.2) t
  change |stoppedAnnularClock _ _ _ _ - F t| < η
  rw [← heq, ← Real.dist_eq, dist_comm]
  exact hj t

/-- The shifted unit-clock convergence holds simultaneously at every integer shift. -/
theorem ae_exists_uniform_limit_integer_shift_stoppedAnnularClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∀ n : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ, Continuous F ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |stoppedAnnularClock (fun z => (dyadicScale j)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z)) δ
              (fun _ => ((t : ℝ).toNNReal)) (ContinuousPath.shift (n : ℝ≥0) p.2) - F t| < η := by
  exact ae_all_iff.mpr fun n =>
    ae_exists_uniform_limit_shift_stoppedAnnularClock hh x hγ hγ2 α hδ n

/-- Uniform limits of the increments on unit blocks give uniform limits on each
finite natural time interval. -/
theorem exists_uniform_limit_on_nat_intervals_of_unit_blocks (A : ℕ → ℝ → ℝ) (hA0 : ∀ j, A j 0 = 0)
    (hblock : ∀ n : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(A j ((n : ℝ) + u) - A j n) - F u| < η) :
    ∀ N : ℕ, ∃ G : ℝ → ℝ, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop,
      ∀ t : ℝ, t ∈ Icc (0 : ℝ) (N : ℝ) → |A j t - G t| < η := by
  intro N
  induction N with
  | zero =>
    refine ⟨fun _ => 0, fun η hη => Eventually.of_forall fun j t ht => ?_⟩
    have ht0 : t = 0 := by
      simp only [Nat.cast_zero, mem_Icc] at ht
      exact le_antisymm ht.2 ht.1
    simp only [ht0, hA0, sub_self, abs_zero]
    exact hη
  | succ N ih =>
    obtain ⟨G, hG⟩ := ih
    obtain ⟨F, hF⟩ := hblock N
    let clamp (t : ℝ) : Icc (0 : ℝ) 1 :=
      ⟨min 1 (max (t - N) 0), ⟨le_min (by norm_num) (le_max_right _ _), min_le_left _ _⟩⟩
    let H (t : ℝ) := if t ≤ N then G t else G N + F (clamp t)
    refine ⟨H, fun η hη => ?_⟩
    have hη2 : 0 < η / 2 := half_pos hη
    filter_upwards [hG (η/2) hη2, hF (η/2) hη2] with j hjG hjF t ht
    by_cases htn : t ≤ N
    · have h := hjG t ⟨ht.1, htn⟩
      simp only [H, htn, ↓reduceIte]
      linarith
    · have hN0 : (0 : ℝ) ≤ N := by positivity
      have htN : (N : ℝ) < t := lt_of_not_ge htn
      have hdiff0 : 0 ≤ t - N := by linarith
      have hdiff1 : t - N ≤ 1 := by push_cast at ht; linarith [ht.2]
      have hclamp : (clamp t : ℝ) = t - N := by
        simp only [clamp, max_eq_left hdiff0, min_eq_right hdiff1]
      have hboundG := hjG N ⟨hN0, le_rfl⟩
      have hboundF := hjF (clamp t)
      have heq : (N : ℝ) + (clamp t : ℝ) = t := by rw [hclamp]; ring
      rw [heq] at hboundF
      simp only [H, htn, ↓reduceIte]
      have habs := abs_add_le (A j N - G N) ((A j t - A j N) - F (clamp t))
      have heq' : A j t - (G N + F (clamp t)) =
          (A j N - G N) + ((A j t - A j N) - F (clamp t)) := by ring
      rw [heq']
      linarith

/-- A shifted unit occupation clock is an increment of the time-integrated clock. -/
theorem stoppedAnnularClock_shift_eq_time_increment (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ) (b : ContinuousPath ℂ)
    (n : ℕ) (u : Icc (0 : ℝ) 1) :
    stoppedAnnularClock f δ (fun _ => ((u : ℝ).toNNReal)) (ContinuousPath.shift n b) =
      (∫ t in (0 : ℝ)..((n : ℝ) + u),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b t.toNNReal)) -
      (∫ t in (0 : ℝ)..(n : ℝ),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b t.toNNReal)) := by
  let g : ℝ → ℝ := fun t => {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b t.toNNReal)
  have hi1 : IntervalIntegrable g volume 0 n := intervalIntegrable_annular_density f hf δ b 0 n
  have hi2 : IntervalIntegrable g volume n ((n : ℝ) + u) :=
    intervalIntegrable_annular_density f hf δ b n ((n : ℝ) + u)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  have heq : stoppedAnnularClock f δ (fun _ => ((u : ℝ).toNNReal)) (ContinuousPath.shift n b) =
      ∫ t in (0 : ℝ)..(u : ℝ), g ((n : ℝ) + t) := by
    rw [stoppedAnnularClock_eq_time_integral _ hf.measurable]
    simp only [NNReal.coe_one, Real.coe_toNNReal', max_eq_left u.2.1,
      min_eq_right u.2.2]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le u.2.1] at ht
    dsimp only [g]
    simp only [ContinuousPath.shift_apply, Real.toNNReal_add (Nat.cast_nonneg n) ht.1,
      Real.toNNReal_natCast]
  rw [heq]
  have htrans := intervalIntegral.integral_comp_add_left g (n : ℝ) (a := 0) (b := (u : ℝ))
  simp only [add_zero] at htrans
  rw [htrans]
  change (∫ t in (n : ℝ)..((n : ℝ) + u), g t) = _
  linarith

/-- At each fixed start, the actual annular clocks have a continuous, nonnegative,
nondecreasing limit, uniformly on every finite time interval under the joint law. -/
theorem ae_exists_locally_uniform_limit_annularClock {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale j)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hdensity : ∀ᵐ ω ∂P, ∀ k : ℕ, Continuous (fun z =>
      (dyadicScale k)^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec k
    have hc : Continuous (hcirc ω (dyadicScale k)) := by
      rw [← funext (hω (dyadicScale k))]
      exact hHc ω (dyadicScale k) (dyadicScale_pos k)
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
        fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
      funext z
      exact (hrec _ z (dyadicScale_pos k)).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log
          (fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  filter_upwards [ae_exists_uniform_limit_integer_shift_stoppedAnnularClock hh x hγ hγ2 α hδ,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hdensity] with p hp hc
  let f (j : ℕ) : ℂ → ℝ := fun z => (dyadicScale j)^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z)
  let g (j : ℕ) (t : ℝ) : ℝ :=
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (f j) (p.2 t.toNNReal)
  let A (j : ℕ) (t : ℝ) : ℝ := ∫ s in (0 : ℝ)..t, g j s
  have hblock : ∀ n : ℕ, ∃ F : Icc (0 : ℝ) 1 → ℝ,
      ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ u : Icc (0 : ℝ) 1,
        |(A j ((n : ℝ) + u) - A j n) - F u| < η := by
    intro n
    obtain ⟨F, _, hF⟩ := hp n
    refine ⟨F, fun η hη => ?_⟩
    filter_upwards [hF η hη] with j hj u
    have heq := stoppedAnnularClock_shift_eq_time_increment (f j) (hc j) δ p.2 n u
    change stoppedAnnularClock (f j) δ _ _ = A j (n + u) - A j n at heq
    rw [← heq]
    exact hj u
  have hnat := exists_uniform_limit_on_nat_intervals_of_unit_blocks A
    (fun j => intervalIntegral.integral_same) hblock
  let B (j : ℕ) (t : ℝ≥0) := A j t
  have hBc (j : ℕ) : Continuous (B j) := by
    have h := intervalIntegral.continuous_primitive
      (fun a b => intervalIntegrable_annular_density (f j) (hc j) δ p.2 a b) 0
    exact h.comp continuous_subtype_val
  have hf0 (j : ℕ) (z : ℂ) : 0 ≤ f j z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos j).le _) (Real.exp_pos _).le
  have hg0 (j : ℕ) (t : ℝ) : 0 ≤ g j t :=
    Set.indicator_nonneg (fun z _ => hf0 j z) _
  have hB0 (j : ℕ) (t : ℝ≥0) : 0 ≤ B j t :=
    intervalIntegral.integral_nonneg_of_forall t.coe_nonneg (hg0 j)
  have hBm (j : ℕ) : Monotone (B j) := by
    intro s t hst
    exact intervalIntegral.integral_mono_interval le_rfl s.coe_nonneg hst
      (Eventually.of_forall (hg0 j))
      (intervalIntegrable_annular_density (f j) (hc j) δ p.2 0 t)
  have hnatB (N : ℕ) : ∃ G : ℝ≥0 → ℝ, ∀ η : ℝ, 0 < η →
      ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ N → |B j t - G t| < η := by
    obtain ⟨G, hG⟩ := hnat N
    refine ⟨fun t => G t, fun η hη => ?_⟩
    filter_upwards [hG η hη] with j hj t ht
    exact hj t ⟨t.coe_nonneg, by exact_mod_cast ht⟩
  exact exists_continuous_monotone_limit_of_uniform_on_nat_intervals B hBc hB0 hBm hnatB

/-- At each fixed start, the actual annular clocks stopped at Brownian exit converge
uniformly on every finite time interval under the joint law. -/
theorem ae_exists_locally_uniform_limit_annularClock_stopped {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ContinuousPath.exitTime D p.2 < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale j)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  filter_upwards [ae_exists_locally_uniform_limit_annularClock hh x hγ hγ2 α hδ,
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_planarBrownian_exitTime_bounded_lt_top x hDb)] with p hp hfin
  obtain ⟨F, hFc, hF0, hFm, hF⟩ := hp
  let r : ℝ≥0 → ℝ≥0 := fun t => min t (ContinuousPath.exitTime D p.2).toNNReal
  have hrc : Continuous r := continuous_id.min continuous_const
  have hrm : Monotone r := fun _ _ h => min_le_min_right _ h
  refine ⟨hfin, F ∘ r, hFc.comp hrc, (fun t => hF0 (r t)), hFm.comp hrm, ?_⟩
  intro T η hη
  filter_upwards [hF T η hη] with j hj t ht
  have hrt : r t ≤ T := (min_le_left _ _).trans ht
  have h := hj (r t) hrt
  have heq : ((r t : ℝ≥0) : ℝ) = min (t : ℝ) (ContinuousPath.exitTime D p.2).toReal := by
    simp only [r, NNReal.coe_min, ENNReal.coe_toNNReal_eq_toReal]
  simpa only [Function.comp_apply, heq] using h

/-- For each fixed start, the locally uniform stopped-clock limit holds for almost every
field and then for almost every Brownian path. -/
theorem ae_field_ae_path_exists_locally_uniform_limit_annularClock_stopped
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hDb : Bornology.IsBounded D) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂planarBrownianMotion x,
      ContinuousPath.exitTime D b < ⊤ ∧
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale j)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale j) z))
                  (b s.toNNReal)) - F t| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  exact Measure.ae_ae_of_ae_prod
    (ae_exists_locally_uniform_limit_annularClock_stopped hh x hγ hγ2 α hδ hDb)

end HarmonicBalls
