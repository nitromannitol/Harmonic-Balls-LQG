import LatticeProb.LQG.GMCContinuumMaximal
import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.LQGBallMassGrid2
import LatticeProb.LQG.LQGSingularScaledLimit
import LatticeProb.LQG.GMCRatioLimitMeasure

/-!
# Continuum convergence of whole-plane GMC test integrals

The circle-average approximations of a whole-plane Gaussian free field converge at all positive
radii to the dyadic LQG measure when tested against a fixed continuous compactly supported function.
The convergence holds on one event for all such tests. For logarithmic insertions it holds on one
event for all tests that vanish near the insertion. The singular approximations also have
uniformly small mass near the insertion at all sufficiently small positive radii.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open LatticeProb.LQG LatticeProb.Gauss

namespace HarmonicBalls

/-- For a fixed compactly supported continuous test, the whole-plane circle-average GMC
approximations converge as the radius tends to zero through positive values. -/
theorem ae_tendsto_integral_lqgApprox_continuum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasure P γ hcirc μ) {g : ℂ → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) :
    ∀ᵐ ω ∂P, Tendsto (fun s : ℝ => ∫ z, g z ∂(lqgApprox γ (hcirc ω) s))
      (𝓝[>] 0) (𝓝 (∫ z, g z ∂(μ ω))) := by
  filter_upwards [hh.ae_exists_tendsto_zero_integral_lqgApprox_sub hγ0 hγ2 hgc hgs, hμ] with ω hu hm
  obtain ⟨u, hu, hb⟩ := hu
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hu' := (Metric.tendsto_atTop.mp hu) (ε / 2) (half_pos hε)
  have hm' := (Metric.tendsto_atTop.mp (hm.tendsto_integral g hgc hgs)) (ε / 2) (half_pos hε)
  obtain ⟨N₁, hN₁⟩ := hu'
  obtain ⟨N₂, hN₂⟩ := hm'
  obtain ⟨N₃, hN₃⟩ := eventually_atTop.mp hb
  let N := max N₁ (max N₂ N₃)
  refine ⟨min 1 (dyadicScale N), lt_min (by norm_num) (dyadicScale_pos_bracket N), ?_⟩
  intro s hs hdist
  have hs0 : 0 < s := hs
  have hsmin : s < min 1 (dyadicScale N) := by simpa [Real.dist_eq, abs_of_pos hs0] using hdist
  obtain ⟨k, hk₁, hk₂⟩ := exists_dyadicScale_bracket hs0 (lt_of_lt_of_le hsmin (min_le_left _ _))
  have hNk : N ≤ k := by
    by_contra h
    have hle : k + 1 ≤ N := by omega
    have := dyadicScale_le_of_le hle
    linarith [lt_of_lt_of_le hsmin (min_le_right (1 : ℝ) (dyadicScale N))]
  have hband := hN₃ k (le_trans (le_trans (le_max_right N₂ N₃) (le_max_right N₁ _)) hNk)
    s (by simpa [dyadicScale_succ_eq_half] using hk₁) hk₂.le
  have huval := hN₁ k (le_trans (le_max_left N₁ _) hNk)
  have hmval := hN₂ k (le_trans (le_trans (le_max_left N₂ N₃) (le_max_right N₁ _)) hNk)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_trans (abs_nonneg _) hband)] at huval
  rw [Real.dist_eq] at hmval ⊢
  calc
    |(∫ z, g z ∂(lqgApprox γ (hcirc ω) s)) - ∫ z, g z ∂(μ ω)| ≤
        |(∫ z, g z ∂(lqgApprox γ (hcirc ω) s)) - ∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))| +
        |(∫ z, g z ∂(lqgApprox γ (hcirc ω) (dyadicScale k))) - ∫ z, g z ∂(μ ω)| := abs_sub_le _ _ _
    _ < ε := by linarith

/-- The whole-plane approximations converge against every compactly supported continuous test
on one common event, as the radius tends to zero through positive values. -/
theorem ae_tendsto_integral_lqgApprox_continuum_all
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasure P γ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun s : ℝ => ∫ z, f z ∂(lqgApprox γ (hcirc ω) s))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂(μ ω))) := by
  obtain ⟨D, hDc, hDcc, hD⟩ := LatticeProb.VagueLimit.exists_countable_determining (X := ℂ)
  have hall : ∀ᵐ ω ∂P, ∀ g ∈ D,
      Tendsto (fun s : ℝ => ∫ z, g z ∂(lqgApprox γ (hcirc ω) s))
        (𝓝[>] 0) (𝓝 (∫ z, g z ∂(μ ω))) :=
    (ae_ball_iff hDc).2 fun g hg =>
      ae_tendsto_integral_lqgApprox_continuum hh hγ0 hγ2 hμ (hDcc g hg).1 (hDcc g hg).2
  filter_upwards [hall, hμ, hh.ae_continuousOn_circle] with ω hω hm hc f hf hfs
  apply tendsto_iff_seq_tendsto.mpr
  intro σ hσ
  have hσpos : ∀ᶠ n in atTop, 0 < σ n := hσ.eventually self_mem_nhdsWithin
  let τ : ℕ → ℝ := fun n => if 0 < σ n then σ n else 1
  have hτpos : ∀ n, 0 < τ n := by
    intro n
    simp only [τ]
    split <;> positivity
  have hτσ : τ =ᶠ[atTop] σ := hσpos.mono fun n hn => ite_eq_left hn
  have hτ : Tendsto τ atTop (𝓝[>] (0 : ℝ)) := hσ.congr' hτσ.symm
  let ρ : ℕ → ℝ := fun n => if n % 2 = 0 then dyadicScale (n / 2) else τ (n / 2)
  have hρeven : ∀ n, ρ (2 * n) = dyadicScale n := by
    intro n
    simp [ρ]
  have hρodd : ∀ n, ρ (2 * n + 1) = τ n := by
    intro n
    simp [ρ]
    congr 1
    omega
  have hρpos : ∀ n, 0 < ρ n := by
    intro n
    simp only [ρ]
    split
    · exact dyadicScale_pos_bracket _
    · exact hτpos _
  have hfinite : ∀ n, IsFiniteMeasureOnCompacts (lqgApprox γ (hcirc ω) (ρ n)) := fun n =>
    GMCRatioLimit.isFiniteMeasureOnCompacts_lqgApprox
      (GMCRatioLimit.continuous_slice hc (hρpos n))
  have hconv : ∀ g ∈ D, ∃ ℓ : ℝ,
      Tendsto (fun n => ∫ z, g z ∂(lqgApprox γ (hcirc ω) (ρ n))) atTop (𝓝 ℓ) := by
    intro g hg
    refine ⟨∫ z, g z ∂(μ ω), LQGSingularScaledLimit.tendsto_of_tendsto_even_odd ?_ ?_⟩
    · simpa only [hρeven] using hm.tendsto_integral g (hDcc g hg).1 (hDcc g hg).2
    · simpa only [hρodd, Function.comp_def] using (hω g hg).comp hτ
  obtain ⟨L, hL⟩ := hD (fun n => lqgApprox γ (hcirc ω) (ρ n)) hfinite hconv f hf hfs
  have he : Tendsto (fun k : ℕ => 2 * k) atTop atTop :=
    StrictMono.tendsto_atTop fun _ _ h => by omega
  have ho : Tendsto (fun k : ℕ => 2 * k + 1) atTop atTop :=
    StrictMono.tendsto_atTop fun _ _ h => by omega
  have hL0 : Tendsto (fun k => ∫ z, f z ∂(lqgApprox γ (hcirc ω) (dyadicScale k)))
      atTop (𝓝 L) := by simpa only [Function.comp_def, hρeven] using hL.comp he
  have hLeq : L = ∫ z, f z ∂(μ ω) := tendsto_nhds_unique hL0 (hm.tendsto_integral f hf hfs)
  have hL1 : Tendsto (fun k => ∫ z, f z ∂(lqgApprox γ (hcirc ω) (τ k)))
      atTop (𝓝 (∫ z, f z ∂(μ ω))) := by
    rw [← hLeq]
    simpa only [Function.comp_def, hρodd] using hL.comp ho
  apply hL1.congr'
  filter_upwards [hτσ] with n hn
  simp only [Function.comp_def, hn]

/-- On one common event, singular approximations converge against every compactly supported
continuous test that vanishes near the insertion. -/
theorem ae_tendsto_integral_singular_lqgApprox_continuum_all_off_origin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      Tendsto (fun s : ℝ =>
        ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) s))
        (𝓝[>] 0) (𝓝 (∫ z, f z ∂(μ ω))) := by
  obtain ⟨μ₀, hμ₀⟩ := hh.exists_isLQGMeasure hγ0 hγ2
  filter_upwards [ae_tendsto_integral_lqgApprox_continuum_all hh hγ0 hγ2 hμ₀,
    hh.ae_continuousOn_circle, hμ] with ω hω hc hm f hf hfs hzero
  obtain ⟨δ, hδ, hfδ⟩ := hzero
  let g : ℂ → ℝ := fun z => f z * max δ ‖z‖ ^ (-(γ * α))
  have hgc : Continuous g := hf.mul
    (LQGMeasureExistenceSingular.continuous_max_norm_rpow hδ _)
  have hgs : HasCompactSupport g := hfs.mul_right
  have heq : ∀ s : ℝ, 0 < s → s ≤ δ →
      (∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) s)) =
        ∫ z, g z ∂(lqgApprox γ (hcirc ω) s) := by
    intro s hs hsδ
    rw [LQGMeasureExistenceSingular.integral_lqgApprox_fieldCircleAverage hs (hcirc ω)
      (GMCRatioLimit.continuous_slice hc hs)]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : ‖z‖ < δ
    · simp [g, hfδ z hz]
    · have hzδ : δ ≤ ‖z‖ := le_of_not_gt hz
      simp [g, max_eq_right hzδ, max_eq_right (hsδ.trans hzδ)]
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] 0,
      (∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) s)) =
        ∫ z, g z ∂(lqgApprox γ (hcirc ω) s) := by
    filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds
      (Iio_mem_nhds hδ)] with s hs hsδ
    exact heq s hs hsδ.le
  have hsing := (hω g hgc hgs).congr' (hevent.mono fun _ h => h.symm)
  have hscale : Tendsto dyadicScale atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨LQGSingularScaledLimit.tendsto_dyadicScale_zero,
      Filter.Eventually.of_forall dyadicScale_pos_bracket⟩
  have hid : (∫ z, g z ∂(μ₀ ω)) = ∫ z, f z ∂(μ ω) :=
    tendsto_nhds_unique (hsing.comp hscale) (hm.tendsto_integral f hf hfs)
  simpa only [hid] using hsing

/-- Away from the insertion point, singular circle-average approximations converge at every
positive radius to the existing dyadic measure when tested against a fixed function. -/
theorem ae_tendsto_integral_singular_lqgApprox_continuum_off_origin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ)
    (hfδ : ∀ z : ℂ, ‖z‖ < δ → f z = 0) :
    ∀ᵐ ω ∂P, Tendsto
      (fun s : ℝ => ∫ z, f z ∂(lqgApprox γ (fieldCircleAverage α (hcirc ω)) s))
      (𝓝[>] 0) (𝓝 (∫ z, f z ∂(μ ω))) := by
  filter_upwards [ae_tendsto_integral_singular_lqgApprox_continuum_all_off_origin
    hh hγ0 hγ2 hμ] with ω hω
  exact hω f hf hfs ⟨δ, hδ, hfδ⟩

/-- On a set where the regularized distance from the insertion lies between one half and one,
the singular approximation is bounded by a fixed multiple of the nonsingular approximation. -/
theorem lqgApprox_fieldCircleAverage_le_of_max_norm_bounds {γ : ℝ} (hγ : 0 ≤ γ)
    (α : ℝ) (h : ℝ → ℂ → ℝ) {t : ℝ} (ht : 0 < t) {A : Set ℂ}
    (hA : MeasurableSet A) (hbound : ∀ z ∈ A, (1 / 2 : ℝ) ≤ max t ‖z‖ ∧ max t ‖z‖ ≤ 1) :
    lqgApprox γ (fieldCircleAverage α h) t A ≤
      ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) * lqgApprox γ h t A := by
  refine lqgApprox_apply_le_of_le_add hγ ht.le hA ?_
  intro z hz
  obtain ⟨hlow, hhigh⟩ := hbound z hz
  have hlog : |Real.log (max t ‖z‖)| ≤ Real.log 2 := by
    rw [abs_le]
    constructor
    · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlow
      rwa [one_div, Real.log_inv] at h
    · exact (Real.log_nonpos (le_of_lt (lt_of_lt_of_le (by norm_num) hlow)) hhigh).trans
        (Real.log_nonneg one_le_two)
  have hmul : |α * Real.log (max t ‖z‖)| ≤ |α| * Real.log 2 := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hlog (abs_nonneg α)
  have hc := circleAverage_log_norm_sub_eq_log_max ht z 0
  simp only [sub_zero] at hc
  simp only [fieldCircleAverage, hc]
  linarith [(abs_le.mp hmul).1]

/-- The singular mass of a ball at a comparable radius is controlled by the continuum
maximal mass of the dilated field. -/
theorem lqgApprox_fieldCircleAverage_ball_le_continuum_iSup {γ : ℝ} (hγ : 0 < γ)
    (α : ℝ) (h : ℝ → ℂ → ℝ) {c t : ℝ} (hc : 0 < c)
    (htlo : (1 / 2 : ℝ) ≤ t) (hthi : t ≤ 1) :
    lqgApprox γ (fieldCircleAverage α h) (c * t) (ball 0 c) ≤
      ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
        (ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h c 0)) *
          ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre c h) u (ball 0 1)) := by
  have ht : 0 < t := by linarith
  have hcomp := lqgApprox_fieldCircleAverage_le_of_max_norm_bounds hγ.le α
    (dilateRecentre c h) ht measurableSet_ball (A := ball 0 1) (by
      intro z hz
      have hz1 : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz).le
      exact ⟨htlo.trans (le_max_left _ _), max_le hthi hz1⟩)
  have hsup : lqgApprox γ (dilateRecentre c h) t (ball 0 1) ≤
      ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre c h) u (ball 0 1) :=
    le_iSup₂_of_le (f := fun u (_ : u ∈ Ioc (0 : ℝ) 1) =>
      lqgApprox γ (dilateRecentre c h) u (ball 0 1)) t ⟨ht, hthi⟩ le_rfl
  calc
    lqgApprox γ (fieldCircleAverage α h) (c * t) (ball 0 c) =
        ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h c 0)) *
          lqgApprox γ (fieldCircleAverage α (dilateRecentre c h)) t (ball 0 1) := by
            simpa only [mul_one] using
              lqgApprox_fieldCircleAverage_dilation_ball hγ.ne' α h hc ht 1
    _ ≤ ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h c 0)) *
          (ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
            lqgApprox γ (dilateRecentre c h) t (ball 0 1)) := mul_le_mul' le_rfl hcomp
    _ ≤ _ := by
      rw [mul_left_comm]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hsup)

/-- The singular mass of a dyadic annulus is controlled by the continuum maximal mass
of the corresponding dilated field. -/
theorem lqgApprox_fieldCircleAverage_annulus_le_continuum_iSup {γ : ℝ} (hγ : 0 < γ)
    (α : ℝ) (h : ℝ → ℂ → ℝ) {c t : ℝ} (hc : 0 < c)
    (ht : 0 < t) (hthi : t ≤ 1) :
    lqgApprox γ (fieldCircleAverage α h) (c * t) (ball 0 c \ ball 0 (c / 2)) ≤
      ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
        (ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h c 0)) *
          ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre c h) u (ball 0 1)) := by
  have hcomp := lqgApprox_fieldCircleAverage_le_of_max_norm_bounds hγ.le α
    (dilateRecentre c h) ht (measurableSet_ball.diff measurableSet_ball)
    (A := ball 0 1 \ ball 0 (1 / 2)) (by
      intro z hz
      have hzlo : (1 / 2 : ℝ) ≤ ‖z‖ := by simpa using hz.2
      have hzhi : ‖z‖ ≤ 1 := (mem_ball_zero_iff.mp hz.1).le
      exact ⟨hzlo.trans (le_max_right _ _), max_le hthi hzhi⟩)
  have hsup : lqgApprox γ (dilateRecentre c h) t (ball 0 1 \ ball 0 (1 / 2)) ≤
      ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre c h) u (ball 0 1) :=
    (measure_mono sdiff_subset).trans (le_iSup₂_of_le (f := fun u (_ : u ∈ Ioc (0 : ℝ) 1) =>
      lqgApprox γ (dilateRecentre c h) u (ball 0 1)) t ⟨ht, hthi⟩ le_rfl)
  calc
    lqgApprox γ (fieldCircleAverage α h) (c * t) (ball 0 c \ ball 0 (c / 2)) =
        ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h c 0)) *
          lqgApprox γ (fieldCircleAverage α (dilateRecentre c h)) t (ball 0 1 \ ball 0 (1 / 2)) := by
            simpa only [mul_one, div_eq_mul_inv, one_mul] using
              lqgApprox_fieldCircleAverage_dilation_annulus hγ.ne' α h hc ht (1 / 2) 1
    _ ≤ ENNReal.ofReal (c ^ (γ * (lqgQ γ - α)) * Real.exp (γ * h c 0)) *
          (ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
            lqgApprox γ (dilateRecentre c h) t (ball 0 1 \ ball 0 (1 / 2))) := mul_le_mul' le_rfl hcomp
    _ ≤ _ := by
      rw [mul_left_comm]
      exact mul_le_mul' le_rfl (mul_le_mul' le_rfl hsup)

/-- A dyadic decomposition bounds the singular mass at every scale in a dyadic band. -/
theorem lqgApprox_fieldCircleAverage_ball_le_continuum_sum {γ : ℝ} (hγ : 0 < γ)
    (α : ℝ) (h : ℝ → ℂ → ℝ) {J k : ℕ} (hJk : J ≤ k) {s : ℝ}
    (hslo : dyadicScale k / 2 ≤ s) (hshi : s ≤ dyadicScale k) :
    lqgApprox γ (fieldCircleAverage α h) s (ball 0 (dyadicScale J)) ≤
      ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
        ∑ j ∈ Finset.Ico J (k + 1),
          ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) *
            Real.exp (γ * h (dyadicScale j) 0)) *
              ⨆ u ∈ Ioc (0 : ℝ) 1,
                lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1) := by
  have hd : ∀ j : ℕ, 0 < dyadicScale j := dyadicScale_pos_bracket
  have hs : 0 < s := lt_of_lt_of_le (div_pos (hd k) (by norm_num)) hslo
  have hscale : ∀ j ≤ k, s / dyadicScale j ≤ 1 := by
    intro j hj
    exact (div_le_one (hd j)).2 (hshi.trans (dyadicScale_le_of_le hj))
  suffices H : ∀ d J : ℕ, J + d = k →
      lqgApprox γ (fieldCircleAverage α h) s (ball 0 (dyadicScale J)) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
          ∑ j ∈ Finset.Ico J (k + 1),
            ENNReal.ofReal (dyadicScale j ^ (γ * (lqgQ γ - α)) *
              Real.exp (γ * h (dyadicScale j) 0)) *
                ⨆ u ∈ Ioc (0 : ℝ) 1,
                  lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1) from
    H (k - J) J (by omega)
  intro d
  induction d with
  | zero =>
    intro J hJ
    rw [add_zero] at hJ
    subst hJ
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton]
    have hlo : (1 / 2 : ℝ) ≤ s / dyadicScale J := by
      apply (le_div_iff₀ (hd J)).2
      linarith
    have hbound := lqgApprox_fieldCircleAverage_ball_le_continuum_iSup hγ α h (hd J)
      hlo (hscale J le_rfl)
    simpa only [mul_div_cancel₀ _ (hd J).ne'] using hbound
  | succ d ih =>
    intro J hJ
    have hsplit : ball (0 : ℂ) (dyadicScale J) ⊆
        (ball 0 (dyadicScale J) \ ball 0 (dyadicScale (J + 1))) ∪ ball 0 (dyadicScale (J + 1)) := by
      rw [sdiff_union_self]
      exact subset_union_left
    have hann := lqgApprox_fieldCircleAverage_annulus_le_continuum_iSup hγ α h (hd J)
      (div_pos hs (hd J)) (hscale J (by omega))
    have hann' : lqgApprox γ (fieldCircleAverage α h) s
        (ball 0 (dyadicScale J) \ ball 0 (dyadicScale (J + 1))) ≤
        ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2))) *
          (ENNReal.ofReal (dyadicScale J ^ (γ * (lqgQ γ - α)) *
            Real.exp (γ * h (dyadicScale J) 0)) *
              ⨆ u ∈ Ioc (0 : ℝ) 1,
                lqgApprox γ (dilateRecentre (dyadicScale J) h) u (ball 0 1)) := by
      simpa only [mul_div_cancel₀ _ (hd J).ne', dyadicScale_succ_eq_half] using hann
    calc
      lqgApprox γ (fieldCircleAverage α h) s (ball 0 (dyadicScale J)) ≤
          lqgApprox γ (fieldCircleAverage α h) s
              (ball 0 (dyadicScale J) \ ball 0 (dyadicScale (J + 1))) +
            lqgApprox γ (fieldCircleAverage α h) s (ball 0 (dyadicScale (J + 1))) :=
        (measure_mono hsplit).trans (measure_union_le _ _)
      _ ≤ _ := add_le_add hann' (ih (J + 1) (by omega))
      _ = _ := by
        rw [← mul_add, Finset.sum_eq_sum_Ico_succ_bot (by omega : J < k + 1)]

/-- Subexponential growth of continuum maximal masses implies uniform smallness of the
singular approximation masses near the insertion at every sufficiently small radius. -/
theorem exists_lqgApprox_fieldCircleAverage_ball_le_continuum {γ α : ℝ} (hγ : 0 < γ)
    (hαQ : α < lqgQ γ) {h : ℝ → ℂ → ℝ} (hZ : ContinuumOriginGrowth γ h) :
    ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      lqgApprox γ (fieldCircleAverage α h) s (ball 0 δ) ≤ ENNReal.ofReal η := by
  intro η hη
  have hσ : 0 < γ * (lqgQ γ - α) := mul_pos hγ (sub_pos.2 hαQ)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set σ := γ * (lqgQ γ - α) with hσdef
  set c := Real.exp (γ * (|α| * Real.log 2)) with hc
  set r := Real.exp (-(σ * Real.log 2 / 2)) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    have : 0 < σ * Real.log 2 / 2 := by positivity
    calc r < Real.exp 0 := Real.exp_lt_exp.2 (by linarith)
      _ = 1 := Real.exp_zero
  have hev := hZ (σ * Real.log 2 / 2) (by positivity)
  have hsmall : ∀ᶠ J : ℕ in atTop, c * (r ^ J / (1 - r)) ≤ η := by
    have ht : Tendsto (fun J : ℕ => c * (r ^ J / (1 - r))) atTop (𝓝 (c * (0 / (1 - r)))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).div_const _).const_mul _
    rw [zero_div, mul_zero] at ht
    exact ht.eventually (ge_mem_nhds hη)
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.1 hev
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (hsmall.and (eventually_ge_atTop J₀))
  obtain ⟨hJη, hJJ₀⟩ := hJ J le_rfl
  refine ⟨dyadicScale J, dyadicScale_pos_bracket J, ?_⟩
  intro s hs hsJ
  have hJ1 : dyadicScale J ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨k, hk₁, hk₂⟩ := exists_dyadicScale_bracket hs (hsJ.trans_le hJ1)
  have hJk : J ≤ k := by
    by_contra h
    have hle : k + 1 ≤ J := by omega
    have hmono := dyadicScale_le_of_le hle
    linarith
  refine (lqgApprox_fieldCircleAverage_ball_le_continuum_sum hγ α h hJk
    (by simpa only [dyadicScale_succ_eq_half] using hk₁) hk₂.le).trans ?_
  have hterm : ∀ j ∈ Finset.Ico J (k + 1),
      ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
          (⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1)) ≤
        ENNReal.ofReal (r ^ j) := by
    intro j hj
    have hjJ : J₀ ≤ j := hJJ₀.trans (Finset.mem_Ico.1 hj).1
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos_bracket j).le _), mul_assoc]
    calc ENNReal.ofReal (dyadicScale j ^ σ) *
          (ENNReal.ofReal (Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1))
        ≤ ENNReal.ofReal (dyadicScale j ^ σ) * ENNReal.ofReal (Real.exp (σ * Real.log 2 / 2 * j)) := by
          gcongr
          exact hJ₀ j hjJ
      _ = ENNReal.ofReal (r ^ j) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (dyadicScale_pos_bracket j).le _), hr,
            ← Real.exp_nat_mul, Real.rpow_def_of_pos (dyadicScale_pos_bracket j), ← Real.exp_add]
          congr 2
          simp only [dyadicScale, Real.log_pow, Real.log_inv]
          ring
  calc ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1),
          ENNReal.ofReal (dyadicScale j ^ σ * Real.exp (γ * h (dyadicScale j) 0)) *
            ⨆ u ∈ Ioc (0 : ℝ) 1, lqgApprox γ (dilateRecentre (dyadicScale j) h) u (ball 0 1)
      ≤ ENNReal.ofReal c * ∑ j ∈ Finset.Ico J (k + 1), ENNReal.ofReal (r ^ j) := by
        gcongr with j hj
        exact hterm j hj
    _ = ENNReal.ofReal (c * ∑ j ∈ Finset.Ico J (k + 1), r ^ j) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => pow_nonneg hr0 j)]
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal
        ((mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hr0 hr1) (Real.exp_pos _).le).trans hJη)

/-- Almost surely, the singular circle-average masses are uniformly small near the
insertion at every sufficiently small positive radius. -/
theorem ae_exists_lqgApprox_fieldCircleAverage_ball_le_continuum
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) :
    ∀ᵐ ω ∂P, ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s → s < δ →
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) s (ball 0 δ) ≤ ENNReal.ofReal η := by
  filter_upwards [hh.ae_continuumOriginGrowth hγ0 hγ2] with ω hω
  exact exists_lqgApprox_fieldCircleAverage_ball_le_continuum hγ0 hαQ hω

end HarmonicBalls
