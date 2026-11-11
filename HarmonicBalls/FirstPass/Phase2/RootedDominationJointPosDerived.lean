import HarmonicBalls.FirstPass.Phase2.RootedDominationJointPos

/-! # Derivation route of the positive-radius joint identity

The route derives `DMSLemmaA10WholePlaneMarkedJointPosStmt`
(RootedDominationJointPos.lean) in three moves: (i) the marked tilt identity for finite families of admissible pairings and
positive-radius circles, from their joint Gaussian law; (ii) passage to GMC; (iii) extension from cylinder tests by a
monotone-class argument. Move (i) is not written in detail in the answer and is not in Mathlib, the pinned packages or
the cited source (DMS arXiv:1409.7055 Lemma A.10 is printed for pairings only: `DMSLemmaA10WholePlaneMarkedSub`,
FirstPass/Frozen/S11i.lean:59). It is therefore recorded below as a named hypothesis, BLOCKED-STEP, and is NOT an input of any
counted theorem. Moves (ii)-(iii) are not yet formalised.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- **Finite-family marked tilt identity, positive-radius circles (BLOCKED-STEP; named hypothesis, not proved).**
For every whole-plane GFF `(hC, hcirc)`, every `α = 0` LQG measure `μ` of `hcirc` at `0 < γ < 2`, every finite family of
test functions `φ i` and of positive-radius circles `c k`, and every measurable `Φ` of the finite observation, integrating
`Φ` of the observation against `μ_ω` on `B₁` and against `P` equals integrating `Φ` of the DMS-shifted observation over
`z ∈ B₁` and `P`. This is the cylinder form of `DMSLemmaA10WholePlaneMarkedJointPosStmt`; the answer's step (i)
(joint Gaussian law) is its only missing ingredient, and steps (ii)-(iii) pass from it to all measurable test functions. -/
def DMSFiniteTiltPosStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → 0 < γ → γ < 2 →
    ∀ (n m : ℕ) (φ : Fin n → ℂ → ℝ) (c : Fin m → CircleParameter)
      (Φ : (Fin n → ℝ) × (Fin m → ℝ) × ℂ → ℝ≥0∞),
      (∀ i, IsTestFunction Set.univ (φ i)) → Measurable Φ →
        ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1,
            Φ ((fun i => hC ω (φ i)), (fun k => hcirc ω (c k).1 (c k).2), z) ∂(μ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
              Φ ((fun i => dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) (φ i)),
                (fun k => dmsShiftedCircle γ z (hcirc ω) (c k).1 (c k).2), z) ∂P ∂volume

end HarmonicBalls
