import Mathlib
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasureAE
import HarmonicBalls.Proofs.Sec11.ClosureScales.RootedShiftProfile
import HarmonicBalls.Proofs.Sec11.ClosureScales.CodedCirclePalm

/-! # Route (A), Palm identity: the marked whole-plane identity (Step M) and the coded Palm identity

Source: the marked whole-plane GMC identity on `B_1` and the coded identity.

* `StepM` (Step M): the marked whole-plane clause, `P(dg) μ_g(dz) = Law(g^{[z]}, z) d²z`.
  The written argument only sketches it.
  It is the genuine staged DMS input and stays an explicit hypothesis of every consumer below. Stated, not proved.
* `RawToProfileStep` (Step B): the canonical profile is a measurable function of the raw pairings, compatible with the
  shift `h ↦ h + f_z`. The written argument gives only the profile-to-raw direction `R(Γ_z c) = g^{[z]}`.
  Historical evidence only: no production consumer uses it. Its consumer
  `palm_omega_of_stepM_stepB_quarantined` is retained for the record only.

The real consumer is `palm_circle_omega_of_stepM`. It replaces Step B by the proved measurable circle decoder
`circleCompatDecoder` and its common-event GFF/DMS compatibility `circleCompatDecoder_gff_identification`, on the actual
carrier `C(CircleDomain, ℝ)` (CodedCirclePalm.lean). It does not use `RawToProfileStep`.

Credit (Leonardo Bonanno): the imports `LQGProfileMeasureAE` and `CodedCirclePalm` reach his Lattice-Probability LQG field
modules `LatticeProb.Bonanno.LQGMetric.Field.*` (pinned lean-v4.35 port); this file uses them only through those imports.
-/

noncomputable section

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- **Step M** (marked whole-plane GMC identity on `B_1`, with the marked version of
[DMS, Lemma A.10, p. 184]). Stated, not proved. For every `Ψ` measurable for the raw pairing
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
a.s. for every `z ∈ B_1` (`Γ_z` is `shiftedProfile`). Stated, not proved. -/
def RawToProfileStep {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (c : Ω → CanonicalProfile) : Prop :=
  IsWholePlaneGFF P hC hcirc → (∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (c ω).1 p = hcirc ω p.1 p.2) →
    ∃ ρ : ((ℂ → ℝ) → ℝ) → CanonicalProfile,
      Measurable[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ] ρ ∧
      (∀ᵐ ω ∂P, ρ (hC ω) = c ω) ∧
      ∀ z ∈ ball (0 : ℂ) 1,
        ∀ᵐ ω ∂P, ρ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) = shiftedProfile γ z (c ω)

/-- **QUARANTINED historical consumer (no production use).** The Ω-form of the coded Palm identity derived from the
quarantined Step B `RawToProfileStep` through the canonical `profileMeasure`: for a nonnegative jointly measurable `Ψ` on
canonical profiles times the marked point, the integral of `Ψ(c, z)` against `profileMeasure γ 0 c` over `B_1` equals
the integral over `B_1` of `Ψ(Γ_z c, z)`. Kept as evidence only; the real Ω-form is `palm_circle_omega_of_stepM`. -/
theorem palm_omega_of_stepM_stepB_quarantined {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
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

/-- **The coded Palm identity, Ω-form, on the actual carrier** (with `C(CircleDomain, ℝ)` as
the profile space). Let `(P, hC, hcirc)` be a whole-plane GFF with LQG measure `μ`, let `rho` be a literal mollifier and
`q : I → CircleDomain` a dense countable family, and let `F ω = circleCodedProfile hρ q (hC ω)` be the actual profile.
For a nonnegative jointly measurable `Ψ` on actual profiles times the marked point,
`∫_Ω ∫_{B_1} Ψ(F ω, z) (circleProfileMeasure γ 0 (F ω))(dz) dP = ∫_{B_1} ∫_Ω Ψ(circleDMSShiftFun γ z (F ω), z) dP d²z`.
Derived from `StepM` (kept as the explicit staged DMS input), the proved measurable decoder `circleCompatDecoder` and its
common-event GFF/DMS compatibility `circleCompatDecoder_gff_identification`; `RawToProfileStep` is not used. -/
theorem palm_circle_omega_of_stepM {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hM : StepM P γ hC hcirc μ)
    {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {I : Type*} [Countable I]
    (q : I → CircleDomain) (hq : DenseRange q)
    (Ψ : C(CircleDomain, ℝ) → ℂ → ℝ≥0∞) (hΨ : Measurable (fun p : C(CircleDomain, ℝ) × ℂ => Ψ p.1 p.2)) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (circleCodedProfile hρ q (hC ω)) z
        ∂(circleProfileMeasure γ 0 (circleCodedProfile hρ q (hC ω))) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1,
          ∫⁻ ω, Ψ (circleDMSShiftFun γ z (circleCodedProfile hρ q (hC ω))) z ∂P ∂volume := by
  have hId := circleCompatDecoder_gff_identification rho hρ q hq
  have hDm : Measurable[pairingMeasSpace] (circleCodedProfile hρ q) := hId.2.2.2.2.2.1
  obtain ⟨-, S, hSm, hSnull, hS⟩ := hId.2.2.2.2.2.2 hG
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := ae_iff.2 hSnull
  have hF : ∀ᵐ ω ∂P, ∀ p : CircleDomain, circleCodedProfile hρ q (hC ω) p = hcirc ω p.1.1 p.1.2 := by
    filter_upwards [hSae] with ω hω
    exact (hS ω hω).1
  have hμc : ∀ᵐ ω ∂P, μ ω = circleProfileMeasure γ 0 (circleCodedProfile hρ q (hC ω)) :=
    ae_lqgMeasure_eq_circleProfileMeasure (F := fun ω => circleCodedProfile hρ q (hC ω)) hμ hF
  have hshift : ∀ z ∈ ball (0 : ℂ) 1, ∀ᵐ ω ∂P,
      circleCodedProfile hρ q (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0))
        = circleDMSShiftFun γ z (circleCodedProfile hρ q (hC ω)) := by
    intro z hz
    filter_upwards [hSae] with ω hω
    exact (hS ω hω).2.2.2 γ z (mem_ball_zero_iff.mp hz).le
  have hΨ' : Measurable[MeasurableSpace.prod (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ)
      inferInstance] (fun p : ((ℂ → ℝ) → ℝ) × ℂ => Ψ (circleCodedProfile hρ q p.1) p.2) :=
    hΨ.comp ((hDm.comp measurable_fst).prodMk measurable_snd)
  have key := hM hG hμ (fun T z => Ψ (circleCodedProfile hρ q T) z) hΨ'
  beta_reduce at key
  have hL : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (circleCodedProfile hρ q (hC ω)) z ∂(μ ω) ∂P
      = ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (circleCodedProfile hρ q (hC ω)) z
          ∂(circleProfileMeasure γ 0 (circleCodedProfile hρ q (hC ω))) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hμc] with ω h
    rw [h]
  have hR : ∫⁻ z in ball (0 : ℂ) 1,
      ∫⁻ ω, Ψ (circleCodedProfile hρ q (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0))) z ∂P ∂volume
      = ∫⁻ z in ball (0 : ℂ) 1,
          ∫⁻ ω, Ψ (circleDMSShiftFun γ z (circleCodedProfile hρ q (hC ω))) z ∂P ∂volume := by
    refine setLIntegral_congr_fun measurableSet_ball (fun z hz => ?_)
    refine lintegral_congr_ae ?_
    filter_upwards [hshift z hz] with ω h
    rw [h]
  rw [hL, hR] at key
  exact key

end HarmonicBalls

end
