import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmStepM
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmMarkedEquality
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmSectionMeasurable
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGKernelMeasurable
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGKernelBorel
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmDMSConstant

/-! # Route (A), Step M: the marked whole-plane identity from the DMS input (P4)

`StepM` (`PalmStepM`) is the marked whole-plane identity `P(dg) μ_g(dz) = Law(g^{[z]}, z) d²z` on `B₁`. Its only literature input is the printed unnormalized total-mass identity of [DMS, Lemma A.10, p. 184],
staged as `DMSLemmaA10WholePlaneUnnormalized` (Proposed/DuplantierMillerSheffield.lean) and kept as the explicit
hypothesis `hU`. From `hU` the proof uses:
* the good set `G` of `exists_lqg_good_set` and the kernel `κ = G.indicator (μ ·|_{B₁})`, measurable by
  `measurable_lqg_kernel` and `measurable_lqg_section`, with `κ = μ|_{B₁}` almost surely;
* `markedLeft_eq_markedRight` (P3.6), which identifies the left and right marked measures;
* the `dmsShiftedPairing` a.e. identity `dmsShiftedPairing_ae_eq` for `‖z‖ ≤ 1` (the DMS constant vanishes a.s.).
`IsWholePlaneGFF` gives `IsProbabilityMeasure P` (`IsWholePlaneGFF.isProbabilityMeasure`). -/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- **Step M from the DMS input**: the marked whole-plane identity `StepM`, proved from the staged
unnormalized total-mass identity `hU` (`DMSLemmaA10WholePlaneUnnormalized`, DMS Lemma A.10 p. 184). -/
theorem stepM_of_dms {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ) :
    StepM P γ hC hcirc μ := by
  unfold StepM
  intro hG hμ Ψ hΨ
  have hprob : IsProbabilityMeasure P := hG.isProbabilityMeasure
  -- the good set `G` and the dyadic versions of the circle averages
  obtain ⟨G, hGm, hGP, hGgood, g, hgm, _, hgN⟩ := exists_lqg_good_set hG hμ
  obtain ⟨κ, hκdef⟩ : ∃ κ : Ω → Measure ℂ, κ = G.indicator (fun ω => (μ ω).restrict (ball (0 : ℂ) 1)) :=
    ⟨_, rfl⟩
  have hκm : Measurable κ := by
    rw [hκdef]
    exact measurable_lqg_kernel hGm hgm hgN hGgood
  have hae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    exact hGP
  have hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1) := by
    filter_upwards [hae] with ω hω
    rw [hκdef]
    exact Set.indicator_of_mem hω _
  have hκs : ∀ S : Set (PairFun × ℂ), MeasurableSet[MeasurableSpace.prod inferInstance inferInstance] S →
      Measurable fun ω => κ ω {z | (toPairFun (hC ω), z) ∈ S} := by
    intro S hS
    rw [hκdef]
    exact measurable_lqg_section hG hGm hgm hgN hGgood hS
  have hML : markedLeft P hC κ = markedRight P γ hC :=
    markedLeft_eq_markedRight hG γ hμ hU hκm hκa hκs
  have hΨ' : Measurable (fun p : PairFun × ℂ => Ψ p.1 p.2) := hΨ
  -- the left side, as an integral against the left marked measure
  have hL : ∫⁻ p, Ψ p.1 p.2 ∂(markedLeft P hC κ) =
      ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω) z ∂(μ ω) ∂P := by
    rw [lintegral_markedLeft P hκs hΨ']
    refine lintegral_congr_ae ?_
    filter_upwards [hκa] with ω hω
    rw [hω]
    rfl
  -- the right side, as an integral against the right marked measure
  have hR : ∫⁻ p, Ψ p.1 p.2 ∂(markedRight P γ hC) =
      ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (shiftedPairing γ z (hC ω)) z ∂P ∂(volume : Measure ℂ) :=
    lintegral_markedRight γ hG hΨ'
  -- for `z ∈ B₁` the DMS shifted pairing is the shifted pairing, almost surely in `ω`
  have hRdms : ∀ z ∈ ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) z ∂P =
      ∫⁻ ω, Ψ (shiftedPairing γ z (hC ω)) z ∂P := by
    intro z hz
    refine lintegral_congr_ae ?_
    filter_upwards [dmsShiftedPairing_ae_eq hG γ (le_of_lt (mem_ball_zero_iff.1 hz))] with ω hω
    rw [hω]
    rfl
  calc ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω) z ∂(μ ω) ∂P
      = ∫⁻ p, Ψ p.1 p.2 ∂(markedLeft P hC κ) := hL.symm
    _ = ∫⁻ p, Ψ p.1 p.2 ∂(markedRight P γ hC) := by rw [hML]
    _ = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (shiftedPairing γ z (hC ω)) z ∂P ∂(volume : Measure ℂ) := hR
    _ = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) z ∂P
          ∂(volume : Measure ℂ) :=
        setLIntegral_congr_fun measurableSet_ball (fun z hz => (hRdms z hz).symm)

end HarmonicBalls

end
