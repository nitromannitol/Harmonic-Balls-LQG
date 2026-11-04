import HarmonicBalls.Proofs.Sec6.RelativelyCompactExhaustion
import HarmonicBalls.Proofs.SecA.Basic

/-! # Compactly supported extensions of harmonic functions

Smooth cutoffs localize functions harmonic near a compact set. The remaining
Brownian generator identification is stated explicitly in the final reduction.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric InnerProductSpace
open scoped NNReal Topology ZeroAtInfty ContDiff

/-- A function smooth on an open set has a smooth, compactly supported
extension agreeing with it on a neighbourhood of any compact subset. -/
theorem exists_compactlySupported_contDiff_eqOn_nhds
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {q : ℂ → ℝ} (hq : ContDiffOn ℝ ∞ q U) :
    ∃ g : ℂ → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ z ∈ K, g =ᶠ[𝓝 z] q := by
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨χ, hχ, hχc, hχU, _, hχone⟩ :=
    exists_cutoff_of_isCompact_subset_isOpen hVc hU hVU
  let g : ℂ → ℝ := fun z => χ z * q z
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact hχ.contDiffAt.mul ((hq z hz).contDiffAt (hU.mem_nhds hz))
    · have heq : g =ᶠ[𝓝 z] (fun _ => 0) := by
        have hzt : z ∉ tsupport χ := fun h => hz (hχU h)
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl |>.mem_nhds hzt] with w hw
        simp only [g, image_eq_zero_of_notMem_tsupport hw, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq heq
  · exact hχc.mul_right
  · intro z hz
    filter_upwards [hVo.mem_nhds (hKV hz)] with w hw
    simp only [g, hχone w (subset_closure hw), one_mul]

/-- If the planar generator vanishes on smooth compactly supported functions
where they are harmonic, a harmonic function admits compact-local generator
extensions on its domain. -/
theorem compact_generator_extensions_of_harmonic
    {U : Set ℂ} (hU : IsOpen U) {q : ℂ → ℝ} (hq : HarmonicOnNhd q U)
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ∀ K : Set ℂ, IsCompact K → K ⊆ U →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z ∈ K, q z = (f : C₀(ℂ, ℝ)) z) ∧
        ∀ z ∈ K, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0 := by
  intro K hK hKU
  have hqd : ContDiffOn ℝ ∞ q U := fun z hz =>
    (_root_.HarmonicAt.analyticAt (hq z hz)).contDiffAt.contDiffWithinAt
  obtain ⟨g, hgd, hgc, hgq⟩ :=
    exists_compactlySupported_contDiff_eqOn_nhds hU hK hKU hqd
  obtain ⟨f, hf, hfgen⟩ := hgen g hgd hgc
  refine ⟨f, ?_, ?_⟩
  · intro z hz
    rw [hf z]
    exact ((hgq z hz).self_of_nhds).symm
  · intro z hz
    apply hfgen z
    exact (harmonicAt_congr_nhds (hgq z hz)).2 (hq z (hKU hz))

open scoped ENNReal ContDiff

/-- The restricted Green-potential stopped bound follows from its harmonicity
off the obstacle and the planar generator identification on smooth test
functions. -/
theorem restricted_greenPotential_stopped_representation_of_harmonic
    {μ : Measure ℂ} {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    {x : ℂ} (hx : x ∈ U \ L)
    (hharm : HarmonicOnNhd (fun z => ∫ y in L, greenFunction U z y ∂μ) (U \ L))
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ENNReal.ofReal (∫ y in L, greenFunction U x y ∂μ) ≤ ∫⁻ path,
      ENNReal.ofReal (∫ y in L,
        greenFunction U (path ((ContinuousPath.exitTime (U \ L) path).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x) := by
  apply restricted_greenPotential_stopped_representation_of_compact_generator_extensions
    hU hUb hL hLU hholder hx
  exact compact_generator_extensions_of_harmonic (hU.sdiff hL.isClosed) hharm hgen

end HarmonicBalls.Section6
