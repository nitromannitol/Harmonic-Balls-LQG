import Mathlib
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasureAE
import HarmonicBalls.Proofs.Sec11.ClosureScales.RootedShiftProfile

/-! # Route (A), Palm identity: the marked whole-plane identity (Step M) and the derivation of eq:r6-palm

Source: notes/sec11-proof/sec11-proof-r8.tex, the marked whole-plane GMC identity on `B_1` (lines 1783-1789) and the
coded identity (lines 1801-1816), with eq:r6-palm at line 1815. Two named Step Props are stated and NOT proved here:

* `StepM` (Step M): the marked whole-plane clause, `P(dg) μ_g(dz) = Law(g^{[z]}, z) d²z` (r8 lines 1783-1789).
  r8 only sketches it (lines 1790-1800, "obtained from the same proof"); the written proof is requested in round 9.
* `RawToProfileStep` (Step B): the canonical profile is a measurable function of the raw pairings, compatible with the
  shift `h ↦ h + f_z`. Not in r8: r8 (lines 1808-1810) gives only the profile-to-raw direction `R(Γ_z c) = g^{[z]}`.

From these, `palm_omega_of_stepM_stepB` derives the coded Palm identity (eq:r6-palm, λ-integrals written over Ω).
-/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- **Step M** (marked whole-plane GMC identity on `B_1`; r8 lines 1783-1789, with the marked version of
[DMS, Lemma A.10, p. 184] claimed in r8 l.1790-1800). Stated, not proved. For every `Ψ` measurable for the raw pairing
σ-algebra `pairingSigmaAlgebra (· ) univ` (tensored with the Borel σ-algebra of the marked point), the marked point `z`
weights `μ_h(dz)` on the left and the shifted field `h + f_z`, `f_z = dmsShiftedPairing`, on the right. -/
def StepM {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ Ψ : ((ℂ → ℝ) → ℝ) → ℂ → ℝ≥0∞,
      Measurable[MeasurableSpace.prod (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ) inferInstance]
        (fun p : ((ℂ → ℝ) → ℝ) × ℂ => Ψ p.1 p.2) →
      ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω) z ∂(μ ω) ∂P
        = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) z ∂P ∂volume

/-- **Step B** (raw-to-profile bridge; NOT in r8). For a whole-plane GFF whose canonical profile is `c`, there is a
measurable map `ρ` from raw pairing functionals to canonical profiles with `ρ(h) = c` a.s., and `ρ(h + f_z) = Γ_z c`
a.s. for every `z ∈ B_1` (`Γ_z` is `shiftedProfile`, r8 lines 1801-1808). Stated, not proved. -/
def RawToProfileStep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (c : Ω → CanonicalProfile) : Prop :=
  IsWholePlaneGFF P hC hcirc → (∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2) →
    ∃ ρ : ((ℂ → ℝ) → ℝ) → CanonicalProfile,
      Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ] ρ ∧
      (∀ᵐ ω ∂P, ρ (hC ω) = c ω) ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        ∀ᵐ ω ∂P, ρ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) = shiftedProfile γ z (c ω)

/-- **The coded Palm identity** (eq:r6-palm, r8 line 1815), in the form with the λ-integrals written over the
probability space: for a nonnegative jointly measurable `Ψ` on canonical profiles times the marked point, the
integral of `Ψ(c, z)` against the coded LQG measure `profileMeasure γ 0 c` over `B_1` equals the integral over
`B_1` of `Ψ(Γ_z c, z)`. Derived from `StepM` and `RawToProfileStep`, using the a.e. identification
`μ_ω = profileMeasure γ 0 (c ω)` (`profileMeasure_ae_eq`, LQGProfileMeasureAE.lean). -/
theorem palm_omega_of_stepM_stepB {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {c : Ω → CanonicalProfile}
    (hcJ : ∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2)
    (hM : StepM P γ hC hcirc μ) (hB : RawToProfileStep P γ hC hcirc c)
    (Ψ : CanonicalProfile → ℂ → ℝ≥0∞) (hΨ : Measurable (fun p : CanonicalProfile × ℂ => Ψ p.1 p.2)) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (c ω) z ∂(profileMeasure γ 0 (c ω)) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (shiftedProfile γ z (c ω)) z ∂P ∂volume := by
  obtain ⟨ρ, hρm, hρc, hρs⟩ := hB hG hcJ
  have hμc : ∀ᵐ ω ∂P, μ ω = profileMeasure γ 0 (c ω) := profileMeasure_ae_eq hμ hcJ
  have hΨ' : Measurable[MeasurableSpace.prod (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ)
      inferInstance] (fun p : ((ℂ → ℝ) → ℝ) × ℂ => Ψ (ρ p.1) p.2) :=
    hΨ.comp ((hρm.comp measurable_fst).prodMk measurable_snd)
  have key := hM hG hμ (fun T z => Ψ (ρ T) z) hΨ'
  have hL : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (ρ (hC ω)) z ∂(μ ω) ∂P
      = ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (c ω) z ∂(profileMeasure γ 0 (c ω)) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hρc, hμc] with ω h1 h2
    rw [h1, h2]
  have hR : ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (ρ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0))) z ∂P ∂volume
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (shiftedProfile γ z (c ω)) z ∂P ∂volume := by
    refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
    refine lintegral_congr_ae ?_
    filter_upwards [hρs z hz] with ω h
    rw [h]
  rw [hL, hR] at key
  exact key



end HarmonicBalls

end
