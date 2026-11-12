import HarmonicBalls.Proofs.Potential.GreenGeneralIdentification
import HarmonicBalls.Proofs.Potential.GreenGeneralBoundary
import HarmonicBalls.Steps.Sec2.GreenPotentialGeneral

/-!
# Hölder continuity of Green potentials on smooth bounded open sets

Under the local volume growth condition, the Green potential
`q(x) = ∫_O G_O(x, y) f(y) μ(dy)` of a bounded density `f` is Hölder continuous on `closure O` for
every smooth bounded open set `O`. This is the general-domain step `GreenPotentialGeneralStep` in the
proof of Proposition 2.5.

The proof follows steps4-final Section 1. The logarithmic potential `V(x) = ∫_O N(x, y) f(y) μ(dy)` is
Hölder continuous on a ball containing `closure O`, and `W := V - q` is harmonic on `O`, continuous on
`closure O`, and equal to `V` on `∂O` (where `q` vanishes). The boundary modulus of continuity for
harmonic functions with Hölder boundary data on domains with uniform exterior discs (barrier argument)
then gives the local Hölder bound for `W`, hence for `q = V - W`; the bound is made global on the
compact set `closure O`.
-/

namespace HarmonicBalls

namespace GreenGeneral

open MeasureTheory Metric Set InnerProductSpace
open scoped NNReal

/-- Local Hölder bound for the Green potential of a bounded density on a smooth bounded open set,
under the volume growth condition on a ball containing it. -/
theorem VolumeGrowth.greenPotential_local_holder {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R βminus βplus : ℝ} (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ x ∈ closure O, ∀ x' ∈ closure O, dist x x' ≤ 1 →
      |(∫ y in O, greenFunction O x y * f y ∂μ) - ∫ y in O, greenFunction O x' y * f y ∂μ| ≤
        C * dist x x' ^ κ := by
  have hOo := isOpen_of_isSmoothBoundedOpen hO
  have hβ : 0 < βplus := hμ.2.1
  set α := greenPotentialHolderExponent βplus with hα_def
  have hα : 0 < α := greenPotentialHolderExponent_pos hβ
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  have hfM' : ∀ᵐ y ∂μ.restrict O, |f y| ≤ |M| := hfM.mono fun y hy => hy.trans (le_abs_self M)
  obtain ⟨C, hC0, hVC⟩ := VolumeGrowth.newtonPotential_holder hR hμ hOo.measurableSet hOR
  obtain ⟨-, hVhol⟩ := hVC f |M| hf (abs_nonneg M) hfM'
  set V : ℂ → ℝ := fun x => ∫ y in O, newtonKernel x y * f y ∂μ with hV_def
  set q : ℂ → ℝ := fun x => ∫ y in O, greenFunction O x y * f y ∂μ with hq_def
  have hVcont : ContinuousOn V (closedBall (0 : ℂ) R) := by
    intro x₀ hx₀
    rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (g := fun x => C * |M| * ‖x - x₀‖ ^ α)
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (eventually_nhdsWithin_of_forall fun x hx => ?_) ?_
    · rw [Real.norm_eq_abs]
      exact hVhol x hx x₀ hx₀
    · have h : Filter.Tendsto (fun x => C * |M| * ‖x - x₀‖ ^ α) (nhdsWithin x₀ (closedBall (0 : ℂ) R))
          (nhds (C * |M| * ‖x₀ - x₀‖ ^ α)) :=
        (((continuous_id.sub continuous_const).norm.rpow_const fun _ => Or.inr hα.le).tendsto x₀
          |>.const_mul _).mono_left nhdsWithin_le_nhds
      simpa [Real.zero_rpow hα.ne'] using h
  have hqc : ContinuousOn q (closure O) := VolumeGrowth.continuousOn_greenPotential hR hμ hO hOR hf hfM
  have hu : HarmonicOnNhd (fun x => V x - q x) O :=
    VolumeGrowth.harmonicOnNhd_newtonPotential_sub_greenPotential hR hμ hO hOR hf hfM
  have huc : ContinuousOn (fun x => V x - q x) (closure O) := (hVcont.mono hcl).sub hqc
  have hq0 : ∀ ξ ∈ frontier O, q ξ = 0 := by
    intro ξ hξ
    have hξO : ξ ∉ O := fun h => hξ.2 (by rw [hOo.interior_eq]; exact h)
    simp [hq_def, greenFunction_of_notMem_left hξO]
  have hub : ∀ ξ ∈ frontier O, V ξ - q ξ = V ξ := fun ξ hξ => by rw [hq0 ξ hξ, sub_zero]
  have hfrB : frontier O ⊆ closedBall (0 : ℂ) R := frontier_subset_closure.trans hcl
  have hgL : ∀ x ∈ frontier O, ∀ y ∈ frontier O, |V x - V y| ≤ C * |M| * dist x y ^ α := by
    intro x hx y hy
    rw [dist_eq_norm]
    exact hVhol x (hfrB hx) y (hfrB hy)
  obtain ⟨B₀, hB₀⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn hVcont
  have hgB : ∀ x ∈ frontier O, |V x| ≤ max B₀ 0 := fun x hx =>
    (Real.norm_eq_abs (V x) ▸ hB₀ x (hfrB hx)).trans (le_max_left _ _)
  have hT : ∀ x ∈ closure O, ∀ y ∈ closure O, dist x y ≤ 2 * R := by
    intro x hx y hy
    have hx' := mem_closedBall_zero_iff.mp (hcl hx)
    have hy' := mem_closedBall_zero_iff.mp (hcl hy)
    linarith [dist_le_norm_add_norm x y]
  obtain ⟨d, hd, hgeom⟩ :=
    HarmonicBalls.SmoothDomainExteriorSphere.exists_half_radius_geometry_of_isSmoothBoundedOpen hO
  have hbm := boundary_modulus hOo subset_rfl hOo hO.1 subset_rfl hd hT hgeom hα
    (mul_nonneg hC0 (abs_nonneg M)) (le_max_right B₀ 0) hgL hgB hu huc hub
  have hW := holder_of_boundary_modulus hOo hO.1 subset_rfl hu huc hub hbm
  set C' := C * |M| + 2 * max B₀ 0 / (barrierConst d (2 * R) * d) with hC'_def
  set κ := α / (α + 2) with hκ_def
  have hκ : 0 < κ := div_pos hα (by linarith)
  have hκα : κ ≤ α := div_le_self hα.le (by linarith)
  refine ⟨C * |M| + C', κ, hκ, fun x hx x' hx' hxx' => ?_⟩
  have h1 := hW x hx x' hx' hxx'
  have h2 : |V x - V x'| ≤ C * |M| * dist x x' ^ α := by
    rw [dist_eq_norm]
    exact hVhol x (hcl hx) x' (hcl hx')
  have h3 : dist x x' ^ α ≤ dist x x' ^ κ :=
    Real.rpow_le_rpow_of_exponent_ge' dist_nonneg hxx' hκ.le hκα
  have h4 : C * |M| * dist x x' ^ α ≤ C * |M| * dist x x' ^ κ :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg hC0 (abs_nonneg M))
  have h5 : q x - q x' = (V x - V x') - ((V x - q x) - (V x' - q x')) := by ring
  change |q x - q x'| ≤ _
  rw [h5]
  calc |(V x - V x') - ((V x - q x) - (V x' - q x'))|
      ≤ |V x - V x'| + |(V x - q x) - (V x' - q x')| := abs_sub _ _
    _ ≤ C * |M| * dist x x' ^ κ + C' * dist x x' ^ κ := add_le_add (h2.trans h4) h1
    _ = (C * |M| + C') * dist x x' ^ κ := by ring

/-- Global Hölder bound on `closure O` for the Green potential of a bounded density. -/
theorem VolumeGrowth.greenPotential_holder {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    {R βminus βplus : ℝ} (hR : 0 < R) (hμ : VolumeGrowth μ R βminus βplus) {O : Set ℂ}
    (hO : IsSmoothBoundedOpen O) (hOR : O ⊆ ball (0 : ℂ) R) {f : ℂ → ℝ} {M : ℝ}
    (hf : AEStronglyMeasurable f (μ.restrict O)) (hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M) :
    ∃ C r : ℝ≥0, 0 < r ∧
      HolderOnWith C r (fun x => ∫ y in O, greenFunction O x y * f y ∂μ) (closure O) := by
  obtain ⟨C, κ, hκ, hloc⟩ := VolumeGrowth.greenPotential_local_holder hR hμ hO hOR hf hfM
  set q : ℂ → ℝ := fun x => ∫ y in O, greenFunction O x y * f y ∂μ with hq_def
  obtain ⟨Q, hQ⟩ := hO.1.isCompact_closure.exists_bound_of_continuousOn
    (VolumeGrowth.continuousOn_greenPotential hR hμ hO hOR hf hfM)
  set D : ℝ := max C (2 * Q) with hD_def
  have hD0 : 0 ≤ max D 0 := le_max_right _ _
  refine ⟨⟨max D 0, hD0⟩, ⟨κ, hκ.le⟩, by exact_mod_cast hκ, holderOnWith_of_bound ?_⟩
  intro x hx x' hx'
  have hp : 0 ≤ dist x x' ^ κ := Real.rpow_nonneg dist_nonneg κ
  rcases le_or_gt (dist x x') 1 with h | h
  · calc |q x - q x'| ≤ C * dist x x' ^ κ := hloc x hx x' hx' h
      _ ≤ max D 0 * dist x x' ^ κ :=
        mul_le_mul_of_nonneg_right ((le_max_left C _).trans (le_max_left _ _)) hp
  · have h1 : 1 ≤ dist x x' ^ κ := Real.one_le_rpow h.le hκ.le
    have hqx := hQ x hx
    have hqx' := hQ x' hx'
    rw [Real.norm_eq_abs] at hqx hqx'
    calc |q x - q x'| ≤ |q x| + |q x'| := abs_sub _ _
      _ ≤ 2 * Q := by linarith
      _ ≤ max D 0 := (le_max_right C _).trans (le_max_left _ _)
      _ ≤ max D 0 * dist x x' ^ κ := le_mul_of_one_le_right hD0 h1

end GreenGeneral

open MeasureTheory Metric Set

/-- The general-domain Green potential estimate of Proposition 2.5 (paper lines 533–537): under local
power-law volume growth, Green potentials of bounded densities are absolutely convergent and Hölder
continuous on the closure of every smooth bounded open set. -/
theorem greenPotentialGeneralStep_holds : GreenPotentialGeneralStep := by
  intro μ hloc hvol O hO f hf
  obtain ⟨R₀, hR₀⟩ := hO.1.subset_ball (0 : ℂ)
  set R := max R₀ 1 with hR_def
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hOR : O ⊆ ball (0 : ℂ) R := hR₀.trans (ball_subset_ball (le_max_left _ _))
  obtain ⟨βminus, βplus, hμ⟩ := hvol R hR
  have hOo := GreenGeneral.isOpen_of_isSmoothBoundedOpen hO
  set M := (eLpNorm f ⊤ (μ.restrict (closure O))).toReal with hM_def
  have hfM' : ∀ᵐ y ∂μ.restrict (closure O), |f y| ≤ M := by
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ.restrict (closure O))] with y hy
    rw [Real.enorm_eq_ofReal_abs] at hy
    exact (ENNReal.ofReal_le_iff_le_toReal hf.eLpNorm_ne_top).1 (hy.trans eLpNormEssSup_le_eLpNorm_top)
  have hfM : ∀ᵐ y ∂μ.restrict O, |f y| ≤ M := ae_restrict_of_ae_restrict_of_subset subset_closure hfM'
  have hf' : AEStronglyMeasurable f (μ.restrict O) := hf.aestronglyMeasurable.mono_set subset_closure
  have hcl : closure O ⊆ closedBall (0 : ℂ) R :=
    (closure_mono hOR).trans closure_ball_subset_closedBall
  exact ⟨fun x hx => GreenGeneral.VolumeGrowth.integrableOn_greenFunction_mul hR hμ hOo hOR hf' hfM x
      (hcl hx), GreenGeneral.VolumeGrowth.greenPotential_holder hR hμ hO hOR hf' hfM⟩

end HarmonicBalls
