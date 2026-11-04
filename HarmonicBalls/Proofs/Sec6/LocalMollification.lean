import HarmonicBalls.Proofs.Sec6.HarmonicCompactExtension
import HarmonicBalls.Proofs.Sec3.PositiveDistribution

/-! # Local mollification of continuous functions

A compactly supported extension and normalized bump convolutions provide the
local uniform approximation needed for regularizing subharmonic functions.
The preservation of the Laplacian sign is a separate analytic step.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric Laplacian
open scoped ContDiff Topology

/-- A function continuous on an open set has a continuous, compactly supported
extension agreeing with it near a given compact subset. -/
theorem exists_compactlySupported_continuous_eqOn_nhds
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : ℂ → ℝ} (hq : ContinuousOn q U) :
    ∃ g : ℂ → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      (∀ z ∈ K, g =ᶠ[𝓝 z] q) ∧
      ∃ δ > 0, cthickening δ K ⊆ U ∧ EqOn g q (cthickening δ K) := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχ, hχc, hχU, _, hχone⟩ :=
    exists_cutoff_of_isCompact_subset_isOpen hVc hU hVU
  obtain ⟨δ, hδ, hδV⟩ := hK.exists_cthickening_subset_open hVo hKV
  let g : ℂ → ℝ := fun z => χ z * q z
  refine ⟨g, ?_, hχc.mul_right, tsupport_mul_subset_left.trans hχU, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ U
    · exact hχ.continuous.continuousAt.mul ((hq z hz).continuousAt (hU.mem_nhds hz))
    · have heq : g =ᶠ[𝓝 z] (fun _ => 0) := by
        have hzt : z ∉ tsupport χ := fun h => hz (hχU h)
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl |>.mem_nhds hzt] with w hw
        simp only [g, image_eq_zero_of_notMem_tsupport hw, zero_mul]
      exact continuousAt_const.congr heq.symm
  · intro z hz
    filter_upwards [hVo.mem_nhds (hKV hz)] with w hw
    simp only [g, hχone w (subset_closure hw), one_mul]
  · refine ⟨δ, hδ, hδV.trans (subset_closure.trans hVU), ?_⟩
    intro z hz
    simp only [g, hχone z (subset_closure (hδV hz)), one_mul]

/-- Normalized mollifications of a compactly supported extension approximate
`q` uniformly on `K`. Their convolution radius can simultaneously be made
arbitrarily small, so they can be used in local distributional estimates. -/
theorem exists_local_mollification
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : ℂ → ℝ} (hq : ContinuousOn q U) :
    ∃ g : ℂ → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U ∧
      (∀ z ∈ K, g =ᶠ[𝓝 z] q) ∧
      (∃ δ > 0, cthickening δ K ⊆ U ∧ EqOn g q (cthickening δ K)) ∧
      ∀ ε > 0, ∀ δ > 0, ∃ N : ℕ, ∀ n ≥ N,
        ContDiff ℝ ∞ (mollify n g) ∧ HasCompactSupport (mollify n g) ∧
        (∀ z ∈ K, |mollify n g z - q z| ≤ ε) ∧
        (mollifierBump n).rOut < δ := by
  obtain ⟨g, hgc, hgs, hgU, hgq, hgeq⟩ :=
    exists_compactlySupported_continuous_eqOn_nhds hU hK hKU hq
  refine ⟨g, hgc, hgs, hgU, hgq, hgeq, ?_⟩
  intro ε hε δ hδ
  obtain ⟨N₁, hN₁⟩ := exists_abs_mollify_sub_le hgc hgs hε
  obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt hδ
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have hn₁ : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn₂ : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have hr : (mollifierBump n).rOut < δ := by
    refine lt_of_le_of_lt ?_ hN₂
    have hcast : (N₂ : ℝ) ≤ n := by exact_mod_cast hn₂
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hsmooth := isTestFunction_mollify (U := Set.univ) hgc hgs
    (δ := 1) (subset_univ _) (n := n) (by
      exact (div_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) n]))
  refine ⟨hsmooth.1.1, hsmooth.1.2.1, ?_, hr⟩
  intro z hz
  rw [← (hgq z hz).self_of_nhds]
  exact hN₁ n hn₁ z

/-- The distributional Laplacian inequality makes each sufficiently small
translated mollifier have nonnegative Laplacian pairing. -/
theorem mollifier_laplacian_pairing_nonneg
    {U K : Set ℂ} {q g : ℂ → ℝ} (hq : LaplacianGE q 0 U)
    {δ : ℝ} (hδU : cthickening δ K ⊆ U)
    (hgeq : EqOn g q (cthickening δ K))
    {z : ℂ} (hz : z ∈ K) {n : ℕ} (hn : (mollifierBump n).rOut ≤ δ) :
    0 ≤ ∫ t, g t * Δ ((mollifierBump n).normed volume) (t - z) := by
  let ρ : ℂ → ℝ := (mollifierBump n).normed volume
  have hsupp : Function.support (fun t => ρ (t - z)) ⊆
      ball z (mollifierBump n).rOut := by
    intro t ht
    have ht' : t - z ∈ ball (0 : ℂ) (mollifierBump n).rOut :=
      ((mollifierBump n).support_normed_eq (μ := (volume : Measure ℂ))) ▸ ht
    rwa [mem_ball, dist_zero_right, ← dist_eq_norm, ← mem_ball] at ht'
  have htsupp : tsupport (fun t => ρ (t - z)) ⊆
      closedBall z (mollifierBump n).rOut :=
    closure_minimal (hsupp.trans ball_subset_closedBall) isClosed_closedBall
  have hball : closedBall z (mollifierBump n).rOut ⊆ cthickening δ K := by
    intro t ht
    exact mem_cthickening_of_dist_le _ z _ _ hz ((mem_closedBall.mp ht).trans hn)
  have htest : IsTestFunction U (fun t => ρ (t - z)) :=
    ⟨(mollifierBump n).contDiff_normed.comp (contDiff_id.sub contDiff_const),
      (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) htsupp,
      htsupp.trans (hball.trans hδU)⟩
  have hpair := (hq.2 _ htest (fun t => (mollifierBump n).nonneg_normed _)).2
  rw [integral_zero_measure] at hpair
  simp_rw [laplacian_comp_sub_const] at hpair
  calc
    0 ≤ ∫ t, q t * Δ ρ (t - z) := hpair
    _ = ∫ t, g t * Δ ρ (t - z) := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      by_cases ht : t ∈ tsupport (fun t => ρ (t - z))
      · rw [hgeq (hball (htsupp ht))]
      · rw [← laplacian_comp_sub_const, laplacian_eq_zero_of_notMem_tsupport ht,
          mul_zero, mul_zero]

end HarmonicBalls.Section6
