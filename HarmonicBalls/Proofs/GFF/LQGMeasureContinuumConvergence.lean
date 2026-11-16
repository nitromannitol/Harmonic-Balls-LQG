import LatticeProb.LQG.GMCRatioLimit
import LatticeProb.LQG.LQGBallMassGrid2
import LatticeProb.LQG.LQGSingularScaledLimit
import LatticeProb.LQG.GMCRatioLimitMeasure

/-!
# Continuum convergence of whole-plane GMC test integrals

The circle-average approximations of a whole-plane Gaussian free field converge at all positive
radii to the dyadic LQG measure when tested against a fixed continuous compactly supported function.
The convergence holds on one event for all such tests. For logarithmic insertions it holds on one
event for all tests that vanish near the insertion.
-/

open MeasureTheory Filter Topology Set
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

end HarmonicBalls
