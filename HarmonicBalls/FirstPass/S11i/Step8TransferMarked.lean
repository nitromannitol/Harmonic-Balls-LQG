import Mathlib
import HarmonicBalls.FirstPass.Frozen.S11i

/-!
# Tonelli transfer of the marked DMS identity (Lemma 11.13, Step 8)

Input: the frozen marked whole-plane identity `DMSLemmaA10WholePlaneMarked` (`FirstPass/Frozen/S11i.lean`), the marked form of
Duplantier-Miller-Sheffield, Lemma A.10 with `D = B₁`, with mark `z`.

Output: if for Lebesgue-a.e. `z ∈ B₁` the shifted field `dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)` lies in `S`
(with mark `z`) for `P`-a.e. `ω`, then for `P`-a.e. `ω` one has `(hC ω, z) ∈ S` for `μ_ω`-a.e. `z ∈ B₁`.

Proof: apply the marked identity to the indicator `Ψ` of `Sᶜ`. The right-hand side vanishes, because the inner `P`-integral
vanishes for a.e. `z ∈ B₁`. So the outer `P`-integral of the inner `μ_ω`-integral vanishes. Its integrand is
`P`-a.e. zero exactly when `Ψ` vanishes `μ_ω`-a.e. on `B₁`, which is the conclusion.

Extra hypothesis `hGae`: the outer integrand is `P`-AEMeasurable. This is the AEMeasurable form, as in
`LQGMeasureSquareMeasurableFrozen` (`FirstPass/Frozen/S11c.lean`), because the LQG measure is specified only almost surely.
It is NOT derivable from `IsLQGMeasureOfField`, `IsWholePlaneGFF` or `hS`: measurability of `ω ↦ μ ω S` is not implied
by the field-level inputs. It is an open item for the operator source-check.
-/

namespace HarmonicBalls.FirstPassS11iStep8Transfer

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- **Tonelli transfer of the marked identity.** From `DMSLemmaA10WholePlaneMarked` (marked DMS Lemma A.10 for `B₁`), the
Lebesgue-a.e. statement `hleb` about the shifted field and mark `z` gives the `P`-a.s. `μ`-a.e. statement about `hC ω`. -/
theorem ae_ae_ball_of_marked_of_ae_volume {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hA10 : DMSLemmaA10WholePlaneMarked P γ hC hcirc μ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (S : Set (((ℂ → ℝ) → ℝ) × ℂ))
    (hS : MeasurableSet[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] S)
    (hleb : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∈ S)
    (hGae : AEMeasurable (fun ω => ∫⁻ z in ball (0 : ℂ) 1,
      Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω, z) ∂(μ ω)) P) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 → (hC ω, z) ∈ S := by
  classical
  set Ψ : (((ℂ → ℝ) → ℝ) × ℂ) → ℝ≥0∞ := Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) with hΨdef
  have hΨ : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ :=
    measurable_const.indicator hS.compl
  -- the right-hand side of the marked identity vanishes
  have hR : ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume = 0 := by
    have hae : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
        ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P = 0 := by
      rw [ae_restrict_iff' measurableSet_ball]
      filter_upwards [hleb] with z hz hzball
      have h0 : ∀ᵐ ω ∂P, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) = 0 := by
        filter_upwards [hz hzball] with ω hω
        exact Set.indicator_of_notMem (by simpa using hω) _
      rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) h0, lintegral_zero]
    rw [lintegral_congr_ae (g := fun _ => (0 : ℝ≥0∞)) hae, lintegral_zero]
  -- the marked identity, applied to Ψ, gives the vanishing of the left-hand side
  have hid := hA10 hGFF hμ Ψ hΨ
  have hL : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω) ∂P = 0 := hid.trans hR
  have hG : (fun ω => ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω)) =ᵐ[P] 0 :=
    (lintegral_eq_zero_iff' hGae).1 hL
  filter_upwards [hG] with ω hω
  -- for such ω, the `μ ω`-integral over `B₁` of `Ψ (hC ω, ·)` vanishes
  have hmz : Measurable fun z : ℂ => Ψ (hC ω, z) :=
    hΨ.comp (measurable_const.prodMk measurable_id)
  have hz0 : (fun z : ℂ => Ψ (hC ω, z)) =ᵐ[(μ ω).restrict (ball (0 : ℂ) 1)] 0 :=
    (lintegral_eq_zero_iff' hmz.aemeasurable).1 hω
  have hz0' : ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 → Ψ (hC ω, z) = 0 :=
    (ae_restrict_iff' measurableSet_ball).1 hz0
  filter_upwards [hz0'] with z hz hzball
  by_contra hnot
  have h1 : Ψ (hC ω, z) = 1 := Set.indicator_of_mem (show (hC ω, z) ∈ Sᶜ from hnot) _
  exact one_ne_zero (h1.symm.trans (hz hzball))

end HarmonicBalls.FirstPassS11iStep8Transfer
