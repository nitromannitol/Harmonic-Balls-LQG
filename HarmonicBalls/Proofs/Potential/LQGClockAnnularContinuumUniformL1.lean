import HarmonicBalls.Proofs.Potential.LQGClockAnnularContinuumConvergence
import HarmonicBalls.Proofs.Potential.LQGClockAnnularGlobalMeasurableLimit

/-! # Uniform L¹ convergence of annular clocks

This file studies uniform-time convergence of annular occupation clocks as the
smoothing radius tends to zero.
-/

open MeasureTheory Filter Set MarkovProcess LatticeProb.LQG
open LatticeProb.LQG.GMCScaleGrid
open scoped Topology ENNReal NNReal

namespace HarmonicBalls

/-- A common integrable bound upgrades almost-everywhere convergence along a
countably generated filter to convergence of the expected distance. -/
theorem tendsto_integral_norm_sub_of_eventually_dominated
    {X ι E : Type*} [MeasurableSpace X] {μ : Measure X}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {l : Filter ι} [l.IsCountablyGenerated] (A : ι → X → E) (F : X → E)
    (hA : ∀ᶠ i in l, AEStronglyMeasurable (A i) μ)
    (hF : AEStronglyMeasurable F μ) (G : X → ℝ) (hG : Integrable G μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖A i x - F x‖ ≤ G x)
    (hconv : ∀ᵐ x ∂μ, Tendsto (fun i => A i x) l (𝓝 (F x))) :
    (∀ᶠ i in l, Integrable (fun x => ‖A i x - F x‖) μ) ∧
      Tendsto (fun i => ∫ x, ‖A i x - F x‖ ∂μ) l (𝓝 0) := by
  have hm : ∀ᶠ i in l, AEStronglyMeasurable (fun x => ‖A i x - F x‖) μ := by
    filter_upwards [hA] with i hi
    exact (hi.sub hF).norm
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖‖A i x - F x‖‖ ≤ G x := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using hx
  have hc : ∀ᵐ x ∂μ, Tendsto (fun i => ‖A i x - F x‖) l (𝓝 0) := by
    filter_upwards [hconv] with x hx
    have hs : Tendsto (fun i => A i x - F x) l (𝓝 (0 : E)) := by
      simpa using hx.sub (tendsto_const_nhds : Tendsto (fun _ : ι => F x) l (𝓝 (F x)))
    simpa only [Function.comp_def, norm_zero] using continuous_norm.continuousAt.tendsto.comp hs
  constructor
  · filter_upwards [hm, hb] with i hi hbi
    exact hG.mono' hi hbi
  · simpa using tendsto_integral_filter_of_dominated_convergence G hm hb hG hc

/-- A nonnegative product-measurable quantity with finite product integral has
an integrable section for almost every first coordinate. -/
theorem ae_integrable_toReal_section_of_lintegral_lt_top
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (S : X × Y → ℝ≥0∞) (hS : AEMeasurable S (μ.prod ν))
    (hfin : (∫⁻ p, S p ∂(μ.prod ν)) < ⊤) :
    ∀ᵐ x ∂μ, Integrable (fun y => (S (x, y)).toReal) ν := by
  let R := hS.mk S
  have hRm : Measurable R := hS.measurable_mk
  have heq : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, S (x, y) = R (x, y) :=
    Measure.ae_ae_of_ae_prod hS.ae_eq_mk
  have hI : (∫⁻ x, ∫⁻ y, R (x, y) ∂ν ∂μ) < ⊤ := by
    rw [← lintegral_prod _ hRm.aemeasurable]
    exact (lintegral_congr_ae hS.ae_eq_mk).symm ▸ hfin
  have hIae : ∀ᵐ x ∂μ, (∫⁻ y, R (x, y) ∂ν) < ⊤ :=
    ae_lt_top' hRm.lintegral_prod_right'.aemeasurable hI.ne
  filter_upwards [heq, hIae] with x hx hix
  have hr : Integrable (fun y => (R (x, y)).toReal) ν :=
    integrable_toReal_of_lintegral_ne_top
      (hRm.comp (measurable_const.prodMk measurable_id)).aemeasurable hix.ne
  exact hr.congr (hx.mono fun y hy => by simpa only using congrArg ENNReal.toReal hy.symm)

/-- The sum of finite-horizon annular grid errors has an integrable
Brownian section for almost every field. -/
theorem exists_ae_integrable_tsum_annular_grid_exit_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ c : ℝ, 0 < c ∧ ∃ K : ℕ,
      ∀ᵐ ω ∂P, ∀ N : ℕ,
        let S : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
          (∑' j : ℕ, ∑ i ∈ Finset.range (gridCount c (j+K) + 1),
            ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
              |(∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D b).toReal,
                {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                  (gridScale (gridCount c) (j+K) i)^(γ^2/2) *
                    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)
                      (gridScale (gridCount c) (j+K) i) z)) (b u.toNNReal)) -
                (∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D b).toReal,
                  {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
                    (dyadicScale (j+K))^(γ^2/2) *
                      Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)
                        (dyadicScale (j+K)) z)) (b u.toNNReal))|)
        Integrable (fun b => (S b).toReal) (planarBrownianMotion x) ∧
          ∀ᵐ b ∂planarBrownianMotion x, S b < ⊤ := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
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
  have hI := ae_integrable_toReal_section_of_lintegral_lt_top _ (AEMeasurable.tsum hm) hint
  have hfinite := Measure.ae_ae_of_ae_prod (ae_lt_top' (AEMeasurable.tsum hm) hint.ne)
  filter_upwards [hI, hfinite] with ω hIω hfω
  exact ⟨hIω, hfω⟩

/-- At a fixed finite horizon, sufficiently small positive smoothing radii
have a common Brownian-integrable bound for almost every field. -/
theorem ae_exists_integrable_bound_continuum_annular_clock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (ρ : ℝ) (G : ContinuousPath ℂ → ℝ), 0 < ρ ∧
      Integrable G (planarBrownianMotion x) ∧
      ∀ᵐ b ∂planarBrownianMotion x, ∀ (s : ℝ), 0 < s → s < ρ →
        ∀ t : ℝ≥0, t ≤ T →
          |∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
            {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              s^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z))
              (b u.toNNReal)| ≤ G b := by
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨c, hc, K, hgrid⟩ :=
    exists_ae_integrable_tsum_annular_grid_exit_clock hh x hγ0 hγ2 α hδ hD hDb
  obtain ⟨η, hη, hcomp⟩ := ae_eventually_annular_exit_clock_grid_comparison hh α γ hδ hc D
  obtain ⟨N, hN⟩ := exists_nat_ge (T : ℝ)
  have heta : ∀ᶠ k in atTop, |η k| ≤ 1 := by
    have h := hη.abs.eventually (Iio_mem_nhds (show |(0 : ℝ)| < 1 by norm_num))
    filter_upwards [h] with k hk
    exact le_of_lt (by simpa using hk)
  filter_upwards [hgrid, hcomp,
    ae_exists_integrable_bound_stopped_annular_clock hh hγ0 hγlt α x hδ hD hDb]
      with ω hgrid hcomp hdyad
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hcomp.and heta)
  obtain ⟨G, hG, hGb⟩ := hdyad
  let A : ℝ → ContinuousPath ℂ → ℝ → ℝ := fun v b t =>
    ∫ u in (0 : ℝ)..min t (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z))
        (b u.toNNReal)
  let S : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
    ∑' j : ℕ, ∑ i ∈ Finset.range (gridCount c (j+K) + 1),
      ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
        |A (gridScale (gridCount c) (j+K) i) b t - A (dyadicScale (j+K)) b t|
  have hSi : Integrable (fun b => (S b).toReal) (planarBrownianMotion x) := (hgrid N).1
  have hSf : ∀ᵐ b ∂planarBrownianMotion x, S b < ⊤ := (hgrid N).2
  refine ⟨dyadicScale (J+K), fun b => 2 * (G b + (S b).toReal),
    dyadicScale_pos _, (hG.add hSi).const_mul 2, ?_⟩
  filter_upwards [hGb, hSf] with b hb hSb s hs hsmall t ht
  obtain ⟨k, hk1, hk2⟩ := exists_dyadicScale_bracket hs
    (hsmall.trans_le (dyadicScale_le_one' (J+K)))
  change s < LatticeProb.LQG.dyadicScale (J+K) at hsmall
  have hJk : J + K ≤ k := by
    by_contra hn
    have hle := dyadicScale_le_of_le (show k+1 ≤ J+K by omega)
    linarith
  have hkK : K ≤ k := by omega
  let j := k - K
  have hj : j + K = k := Nat.sub_add_cancel hkK
  have hs1 : dyadicScale k / 2 ≤ s := by
    change LatticeProb.LQG.dyadicScale k / 2 ≤ s
    simpa only [dyadicScale_succ_eq_half] using hk1
  obtain ⟨i, hi, hcmp⟩ := (hJ k (by omega)).1 s hs1 hk2.le
  let r := gridScale (gridCount c) k i
  let u : Icc (0 : ℝ) N := ⟨t, ⟨t.coe_nonneg, le_trans (show (t : ℝ) ≤ T from ht) hN⟩⟩
  have hle : ENNReal.ofReal |A r b t - A (dyadicScale k) b t| ≤ S b := by
    have hle1 := le_iSup (fun v : Icc (0 : ℝ) N => ENNReal.ofReal
      |A r b v - A (dyadicScale k) b v|) u
    have hle2 : (⨆ v : Icc (0 : ℝ) N, ENNReal.ofReal
        |A r b v - A (dyadicScale k) b v|) ≤
        ∑ i ∈ Finset.range (gridCount c (j+K) + 1),
          ⨆ v : Icc (0 : ℝ) N, ENNReal.ofReal
            |A (gridScale (gridCount c) (j+K) i) b v - A (dyadicScale (j+K)) b v| := by
      rw [hj]
      dsimp only [r]
      exact Finset.single_le_sum (f := fun i : ℕ =>
        ⨆ v : Icc (0 : ℝ) N, ENNReal.ofReal
          |A (gridScale (gridCount c) k i) b v - A (dyadicScale k) b v|)
        (fun _ _ => by positivity) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
    exact hle1.trans (hle2.trans (by
      dsimp only [S]
      exact ENNReal.le_tsum (f := fun j : ℕ =>
        ∑ i ∈ Finset.range (gridCount c (j+K) + 1),
          ⨆ v : Icc (0 : ℝ) N, ENNReal.ofReal
            |A (gridScale (gridCount c) (j+K) i) b v - A (dyadicScale (j+K)) b v|) j))
  have hdiff : |A r b t - A (dyadicScale k) b t| ≤ (S b).toReal := by
    have h := ENNReal.toReal_mono hSb.ne hle
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h
  have hdy : |A (dyadicScale k) b t| ≤ G b := hb k t
  have hr : |A r b t| ≤ G b + (S b).toReal := by
    have h := abs_add_le (A r b t - A (dyadicScale k) b t) (A (dyadicScale k) b t)
    have heq : A r b t - A (dyadicScale k) b t + A (dyadicScale k) b t = A r b t := by ring
    rw [heq] at h
    linarith
  have hcmp' : |A s b t - A r b t| ≤ η k * A r b t := hcmp b t
  have heta' : η k * A r b t ≤ |A r b t| := by
    calc
      _ ≤ |η k| * |A r b t| := by rw [← abs_mul]; exact le_abs_self _
      _ ≤ 1 * |A r b t| := mul_le_mul_of_nonneg_right (hJ k (by omega)).2 (abs_nonneg _)
      _ = _ := one_mul _
  have htri := abs_add_le (A s b t - A r b t) (A r b t)
  have heq : A s b t - A r b t + A r b t = A s b t := by ring
  rw [heq] at htri
  change |A s b t| ≤ 2 * (G b + (S b).toReal)
  linarith

/-- For almost every field, the actual exit-stopped annular clocks converge
in Brownian L¹ in the uniform norm as the positive radius tends to zero. -/
theorem ae_exists_continuum_stopped_annular_clock_uniform_L1_limit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∃ (A : ℝ → ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ))
        (F : ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ)),
      (∀ s, 0 < s → ∀ b t, A s b t =
        ∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            s^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z)) (b u.toNNReal)) ∧
      Measurable F ∧
      (∀ᵐ b ∂planarBrownianMotion x,
        Tendsto (fun s => A s b) (𝓝[>] (0 : ℝ)) (𝓝 (F b))) ∧
      (∀ᶠ s in 𝓝[>] (0 : ℝ),
        Integrable (fun b => ‖A s b - F b‖) (planarBrownianMotion x)) ∧
      Tendsto (fun s => ∫ b, ‖A s b - F b‖ ∂planarBrownianMotion x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  filter_upwards [hcont, ae_recentered_inserted_circle_average hh α,
    ae_exists_integrable_bound_continuum_annular_clock hh x hγ0 hγ2 α hδ hD hDb T,
    ae_exists_stopped_annular_clock_uniform_L1_limit hh x hγ0 hγ2 α hδ hD hDb T,
    ae_field_ae_path_annular_exit_clock_continuum_convergence hh x hγ0 hγ2 α hδ hD hDb]
      with ω hcont hrec hbound hdyad hconv
  obtain ⟨ρ, G, hρ, hG, hbound⟩ := hbound
  obtain ⟨Ad, F, hAd, hFm, hFlim, _, _⟩ := hdyad
  let Z : ℝ → ℂ → ℝ := fun r z => r^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)
  have hc (r : ℝ) (hr : 0 < r) : Continuous (Z r) := by
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
        fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
      funext z
      exact (hrec _ z hr).symm
    have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
      rw [heq]
      exact ((hcont _ hr).sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
  let A : ℝ → ContinuousPath ℂ → C(Icc (0 : ℝ) (T : ℝ), ℝ) := fun r b =>
    if hr : 0 < r then
      ⟨fun t => ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (Z r) (b s.toNNReal),
        (intervalIntegral.continuous_primitive
          (fun a c => intervalIntegrable_annular_density (Z r) (hc r hr) δ b a c) 0).comp
            (continuous_subtype_val.min continuous_const)⟩
    else 0
  have hAeq (r : ℝ) (hr : 0 < r) (b : ContinuousPath ℂ) (t : Icc (0 : ℝ) T) :
      A r b t = ∫ s in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (Z r) (b s.toNNReal) := by
    simp only [A, dite_eq_left hr, ContinuousMap.coe_mk]
  have hAm (r : ℝ) (hr : 0 < r) : Measurable (A r) := by
    apply ContinuousMap.measurable_iff_eval.mpr
    intro t
    simpa only [hAeq r hr, Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using
      measurable_stopped_annular_time_integral hD (Z r) (hc r hr) δ ((t : ℝ).toNNReal)
  have hscale : Tendsto dyadicScale atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Eventually.of_forall fun k => dyadicScale_pos k⟩
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hAdEq (k : ℕ) (b : ContinuousPath ℂ) : A (dyadicScale k) b = Ad k b := by
    ext t
    rw [hAeq _ (dyadicScale_pos k), hAd]
  have hlimit : ∀ᵐ b ∂planarBrownianMotion x,
      Tendsto (fun r => A r b) (𝓝[>] (0 : ℝ)) (𝓝 (F b)) := by
    filter_upwards [hconv, hFlim] with b hb hbd
    obtain ⟨_, L, hLc, _, _, hL⟩ := hb
    let C : C(Icc (0 : ℝ) (T : ℝ), ℝ) :=
      ⟨fun t => L ((t : ℝ).toNNReal), hLc.comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩
    have hAC : Tendsto (fun r => A r b) (𝓝[>] (0 : ℝ)) (𝓝 C) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      obtain ⟨q, hq, hqL⟩ := hL T (ε/2) (half_pos hε)
      have hqev : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < q :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hq)
      filter_upwards [self_mem_nhdsWithin, hqev] with r hr hrq
      have hle : ‖A r b - C‖ ≤ ε/2 := by
        apply (ContinuousMap.norm_le (A r b - C) (le_of_lt (half_pos hε))).2
        intro t
        have ht : (t : ℝ).toNNReal ≤ T := by
          exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
        have hh := (hqL r hr hrq ((t : ℝ).toNNReal) ht).le
        simpa only [hAeq r hr, C, ContinuousMap.sub_apply, ContinuousMap.coe_mk,
          Real.norm_eq_abs, Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk, Z] using hh
      rw [dist_eq_norm]
      exact lt_of_le_of_lt hle (half_lt_self hε)
    have heq : C = F b := tendsto_nhds_unique (hAC.comp hscale) (by simpa only [Function.comp_def, hAdEq] using hbd)
    simpa only [heq] using hAC
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r < ρ := by
    filter_upwards [self_mem_nhdsWithin, (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hρ))] with r hr hrρ
    exact ⟨hr, hrρ⟩
  have hAb : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ᵐ b ∂planarBrownianMotion x, ‖A r b‖ ≤ G b := by
    filter_upwards [hsmall] with r hr
    filter_upwards [hbound] with b hb
    have hG0 : 0 ≤ G b := (abs_nonneg _).trans (hb r hr.1 hr.2 0 (bot_le : (0 : ℝ≥0) ≤ T))
    apply (ContinuousMap.norm_le (A r b) hG0).2
    intro t
    have ht : (t : ℝ).toNNReal ≤ T := by
      exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
    simpa only [hAeq r hr.1, Z, Real.norm_eq_abs,
      Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using hb r hr.1 hr.2 ((t : ℝ).toNNReal) ht
  have hFb : ∀ᵐ b ∂planarBrownianMotion x, ‖F b‖ ≤ G b := by
    filter_upwards [hlimit, hbound] with b hb hbb
    apply le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hb)
    filter_upwards [hsmall] with r hr
    have hG0 : 0 ≤ G b := (abs_nonneg _).trans (hbb r hr.1 hr.2 0 (bot_le : (0 : ℝ≥0) ≤ T))
    apply (ContinuousMap.norm_le (A r b) hG0).2
    intro t
    have ht : (t : ℝ).toNNReal ≤ T := by
      exact NNReal.coe_le_coe.mp (by simpa [Real.toNNReal_of_nonneg t.property.1] using t.property.2)
    simpa only [hAeq r hr.1, Z, Real.norm_eq_abs,
      Real.toNNReal_of_nonneg t.property.1, NNReal.coe_mk] using hbb r hr.1 hr.2 ((t : ℝ).toNNReal) ht
  have hdist : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ᵐ b ∂planarBrownianMotion x,
      ‖A r b - F b‖ ≤ 2 * G b := by
    filter_upwards [hAb] with r hr
    filter_upwards [hr, hFb] with b hb hf
    calc
      ‖A r b - F b‖ ≤ ‖A r b‖ + ‖F b‖ := norm_sub_le _ _
      _ ≤ G b + G b := add_le_add hb hf
      _ = 2 * G b := by ring
  have hm : ∀ᶠ r in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (A r) (planarBrownianMotion x) := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hAm r hr).aestronglyMeasurable
  obtain ⟨hi, hl⟩ := tendsto_integral_norm_sub_of_eventually_dominated A F hm hFm.aestronglyMeasurable
    (fun b => 2 * G b) (hG.const_mul 2) hdist hlimit
  exact ⟨A, F, fun r hr b t => hAeq r hr b t, hFm, hlimit, hi, hl⟩

end HarmonicBalls
