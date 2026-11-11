import HarmonicBalls.FirstPass.Phase2.RootedDominationDerived
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.FirstPass.Frozen.S11aj
import HarmonicBalls.Proposed.LQG

/-! # Joint marked DMS identity: conditional derivation of `LocalRootedFieldMeasureDomination` (Lemma 8.2)

Task `fp-audit-r1-b2-rooted-domination`, addendum (lead lh, 02:02 UTC). Worker z3.

The pairings-only marked identity `DMSLemmaA10WholePlaneMarkedSub` (`FirstPass/Frozen/S11i.lean:59`) sees the field only
through `hC`, while the rooted observation of the α₀-measure needs the circle profile `hcirc` as well (route
`notes/fp-gaps/CHATGPT-219-hb-8-2-R9-hL1-hWeyl-PRO.md`, section 4). This file states the joint marked identity
`DMSLemmaA10WholePlaneMarkedJoint` (Duplantier-Miller-Sheffield, arXiv:1409.7055, Lemma A.10, marked and with the
circle averages of the shifted field). It is a candidate input: PENDING SOURCE CHECK R26. It is not a binder of any
counted theorem and is not staged in `Frozen/` or `Proposed/`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The circle averages of the DMS-shifted field `h + f_z + κ`, with `f_z = dmsShift γ z` and the constant
`κ = dmsConstant γ z (h_1(0))`, given the circle averages `hc` of `h`: at radius `r` and centre `x`,
`hc r x + Av_{∂B_r(x)} f_z + κ`. This is the circle-profile companion of `dmsShiftedPairing`. -/
noncomputable def dmsShiftedCircle (γ : ℝ) (z : ℂ) (hc : ℝ → ℂ → ℝ) : ℝ → ℂ → ℝ :=
  fun r x => hc r x + Real.circleAverage (dmsShift γ z) x r + dmsConstant γ z (hc 1 0)

/-- **Joint marked DMS identity (candidate input, PENDING SOURCE CHECK R26).** Duplantier-Miller-Sheffield,
arXiv:1409.7055, Lemma A.10, in the marked form that also sees the circle profile `hcirc`: for a whole-plane GFF `(hC, hcirc)`
and the `α = 0` LQG measure `μ` of `hcirc` at parameter `0 < γ < 2`, and for every measurable test `Ψ` of the triple
(pairing, circle profile, mark), integrating `Ψ` against `μ_ω` restricted to the unit ball and against `P` equals
integrating the shifted triple over the mark `z` in `B₁` and over `P`. Not a binder of any counted theorem. -/
def DMSLemmaA10WholePlaneMarkedJoint {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) : Prop :=
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ → 0 < γ → γ < 2 →
    ∀ Ψ : (((ℂ → ℝ) → ℝ) × (ℝ → ℂ → ℝ) × ℂ) → ℝ≥0∞,
      Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance] Ψ →
        ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, hcirc ω, z) ∂(μ ω) ∂P
          = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω,
              Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), dmsShiftedCircle γ z (hcirc ω), z) ∂P ∂volume

/-- The joint marked identity for every whole-plane GFF and every `α = 0` LQG measure, in the universe of the
counted statements. This is the shape of the input `hJoint` of the conditional theorem. -/
def DMSLemmaA10WholePlaneMarkedJointStmt : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ), DMSLemmaA10WholePlaneMarkedJoint P γ hC hcirc μ

end HarmonicBalls
