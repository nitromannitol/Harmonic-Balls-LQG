import HarmonicBalls.Proofs.Sec6.HarmonicIntegral
import HarmonicBalls.Proofs.Sec3.Basic

/-! # Uniform bounds for the Green kernel away from the diagonal

A bounded planar domain has a constant harmonic minorant of each Newtonian
kernel. On disjoint compact sets this gives a uniform Green-kernel bound.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Metric InnerProductSpace ProbabilityTheory MarkovProcess
open scoped NNReal ENNReal ContDiff ZeroAtInfty

/-- The Green kernel is uniformly bounded on two disjoint compact subsets of a
bounded domain. -/
theorem exists_uniform_bound_greenFunction {U K L : Set ℂ}
    (hU : Bornology.IsBounded U) (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ U) (hLU : L ⊆ U) (hKL : Disjoint K L) :
    ∃ C : ℝ, ∀ z ∈ K, ∀ x ∈ L, |greenFunction U z x| ≤ C := by
  obtain ⟨R, hR⟩ := hU.exists_norm_le
  have hminor : ∀ z ∈ U, IsHarmonicMinorant U (newtonKernelEReal z)
      (fun _ => -(2 * Real.pi)⁻¹ * Real.log (2 * R)) := by
    intro z hz
    apply isHarmonicMinorant_const_newtonKernelEReal
    intro x hx
    rw [mem_closedBall, dist_eq_norm]
    have hxR := hR x hx
    have hzR := hR z hz
    calc
      ‖x - z‖ ≤ ‖x‖ + ‖z‖ := norm_sub_le x z
      _ ≤ 2 * R := by linarith
  have hcont : ContinuousOn (fun p : ℂ × ℂ => newtonKernel p.1 p.2) (K ×ˢ L) := by
    unfold newtonKernel
    refine continuousOn_const.mul (ContinuousOn.log
      (continuous_fst.continuousOn.sub continuous_snd.continuousOn).norm ?_)
    intro p hp
    exact norm_ne_zero_iff.2 (sub_ne_zero.2 (fun h =>
      (Set.disjoint_left.mp hKL) hp.1 (h ▸ hp.2)))
  obtain ⟨C, hC⟩ := (hK.prod hL).exists_bound_of_continuousOn hcont
  refine ⟨C + (2 * Real.pi)⁻¹ * Real.log (2 * R), ?_⟩
  intro z hz x hx
  have hne : z ≠ x := fun h => (Set.disjoint_left.mp hKL) hz (h ▸ hx)
  have hlow := (hminor z (hKU hz)).le_greatestHarmonicMinorant x
  have hup : greatestHarmonicMinorant U (newtonKernelEReal z) x ≤ (newtonKernel z x : EReal) := by
    simpa [newtonKernelEReal, Ne.symm hne] using
      greatestHarmonicMinorant_le (u := newtonKernelEReal z) (hLU hx)
  have hreal := EReal.toReal_le_toReal hlow (EReal.coe_ne_bot _)
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) hup)
  rw [EReal.toReal_coe] at hreal
  have hn := hC (z, x) ⟨hz, hx⟩
  rw [Real.norm_eq_abs] at hn
  rw [abs_of_nonneg (greenFunction_nonneg hU z x), greenFunction,
    ite_eq_left ⟨hKU hz, hLU hx, hne⟩]
  linarith [le_abs_self (newtonKernel z x)]

/-- Hölder regularity and the kernel's harmonicity and measurability imply
harmonicity of the restricted Green potential on the complement of its support. -/
theorem harmonicOnNhd_restricted_greenPotential_of_kernel_and_holder_of_bounded
    {U L : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U) {μ : Measure ℂ} (hfinite : μ L < ⊤)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hkernel : ∀ x ∈ L, HarmonicOnNhd (fun z => greenFunction U z x) (U \ L))
    (hmeas : Measurable (fun p : ℂ × ℂ => greenFunction U p.2 p.1)) :
    HarmonicOnNhd (fun z => ∫ x in L, greenFunction U z x ∂μ) (U \ L) := by
  apply harmonicOnNhd_restricted_greenPotential_of_kernel_and_holder hU hL hLU hfinite hholder hkernel hmeas
  intro c r hr hsub
  have hsU : sphere c r ⊆ U := sphere_subset_closedBall.trans (hsub.trans sdiff_subset)
  have hdis : Disjoint (sphere c r) L := Set.disjoint_left.mpr (fun z hz hzL =>
    (hsub (sphere_subset_closedBall hz)).2 hzL)
  obtain ⟨C, hC⟩ := exists_uniform_bound_greenFunction hUb (isCompact_sphere c r) hL hsU hLU hdis
  exact ⟨C, fun x hx z hz => hC z hz x hx⟩

/-- A restricted Green potential in a disc is harmonic off its compact
support whenever the disc Green-potential operator has Hölder regularity. -/
theorem harmonicOnNhd_restricted_greenPotential_ball_of_holder
    {R : ℝ} {L : Set ℂ} (hL : IsCompact L) (hLU : L ⊆ ball (0 : ℂ) R)
    {μ : Measure ℂ} (hfinite : μ L < ⊤)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure (ball (0 : ℂ) R))) →
      (∀ x ∈ closure (ball (0 : ℂ) R),
        IntegrableOn (fun y => greenFunction (ball 0 R) x y * f y) (ball 0 R) μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in ball 0 R, greenFunction (ball 0 R) x y * f y ∂μ)
          (closure (ball 0 R))) :
    HarmonicOnNhd (fun z => ∫ x in L, greenFunction (ball 0 R) z x ∂μ) (ball 0 R \ L) := by
  apply harmonicOnNhd_restricted_greenPotential_of_kernel_and_holder_of_bounded
    isOpen_ball isBounded_ball hL hLU hfinite hholder
  · intro x hx
    have hh := (harmonicOnNhd_greenFunction_ball (hLU hx)).mono
      (show ball (0 : ℂ) R \ L ⊆ ball 0 R \ {x} from fun z hz =>
        ⟨hz.1, fun hzx => hz.2 (hzx ▸ hx)⟩)
    simpa only [greenFunction_ball_comm R] using hh
  · exact (measurable_greenFunction_ball_uncurry R).comp (measurable_snd.prodMk measurable_fst)

/-- In a disc, the stopped restricted-potential bound follows from Hölder
regularity and the planar Brownian generator on smooth compactly supported
functions. -/
theorem restricted_greenPotential_ball_stopped_representation_of_holder
    {μ : Measure ℂ} {R : ℝ} {L : Set ℂ} (hL : IsCompact L)
    (hLU : L ⊆ ball (0 : ℂ) R) (hfinite : μ L < ⊤)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure (ball (0 : ℂ) R))) →
      (∀ x ∈ closure (ball (0 : ℂ) R),
        IntegrableOn (fun y => greenFunction (ball 0 R) x y * f y) (ball 0 R) μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in ball 0 R, greenFunction (ball 0 R) x y * f y ∂μ)
          (closure (ball 0 R)))
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) R \ L)
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, HarmonicAt g z →
          (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0) :
    ENNReal.ofReal (∫ y in L, greenFunction (ball 0 R) x y ∂μ) ≤ ∫⁻ path,
      ENNReal.ofReal (∫ y in L,
        greenFunction (ball 0 R) (path ((ContinuousPath.exitTime (ball 0 R \ L) path).toNNReal)) y ∂μ)
          ∂(planarBrownianMotion x) := by
  exact restricted_greenPotential_stopped_representation_of_harmonic isOpen_ball isBounded_ball
    hL hLU hholder hx (harmonicOnNhd_restricted_greenPotential_ball_of_holder hL hLU hfinite hholder) hgen

end HarmonicBalls.Section6
