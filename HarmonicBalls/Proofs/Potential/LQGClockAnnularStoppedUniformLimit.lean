import HarmonicBalls.Proofs.Potential.LQGClockAnnularLimitRegularity
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability

/-! # Stopped annular clock limits

Uniform convergence on the unit interval passes to the Brownian exit time.
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

end HarmonicBalls
