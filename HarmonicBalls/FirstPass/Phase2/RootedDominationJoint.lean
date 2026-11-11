import HarmonicBalls.FirstPass.Phase2.RootedDominationDerived
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.FirstPass.Frozen.S11aj
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.FirstPass.Closure.LocalRootKernelAc

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

/-- The normalised root kernel is a finite kernel (it is `weightedRestrictionKernel` with unit weight). -/
instance localRootKernel_isFiniteKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P) : IsFiniteKernel (localRootKernel P lam hlam) := by
  unfold localRootKernel
  infer_instance

/-! ## Step 2-3 of route section 5: from the Palm integral to the rooted law -/

/-- **Palm replacement (route Steps 2-3).** The unnormalised Palm measure dominates the rooted law. Let `O` be a
measurable observation of a root `(ω, z)` and `S` a measurable set of observations. If for `P`-a.e. `ω` the set of
roots `z ∈ D` with `O(ω, z) ∈ S` is null for `λ_ω|B₁`, then the rooted law `(P ⊗ₘ K_root).restrict (z ∈ D)` assigns
`S` mass zero. The normalised root kernel `K_root` is a.s. absolutely continuous with respect to `λ_ω|B₁`
(`localRootKernel_ac_ae`, Lemma 8.2 proof). -/
theorem rootedLaw_apply_eq_zero_of_palm {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [SFinite P] (lam : Ω → Measure ℂ) (hlam : AEMeasurable lam P)
    {D : Set ℂ} (hD : MeasurableSet D) (O : Ω × ℂ → X) (hO : Measurable O)
    {S : Set X} (hS : MeasurableSet S)
    (hzero : ∀ᵐ ω ∂P, (lam ω).restrict (ball 0 1) (Prod.mk ω ⁻¹' (O ⁻¹' S ∩ Prod.snd ⁻¹' D)) = 0) :
    ((P ⊗ₘ localRootKernel P lam hlam).restrict (Prod.snd ⁻¹' D)).map O S = 0 := by
  have hA : MeasurableSet (O ⁻¹' S ∩ Prod.snd ⁻¹' D) := (hO hS).inter (measurable_snd hD)
  rw [Measure.map_apply hO hS, Measure.restrict_apply (hO hS),
    Measure.compProd_apply hA]
  have hae : ∀ᵐ ω ∂P, localRootKernel P lam hlam ω (Prod.mk ω ⁻¹' (O ⁻¹' S ∩ Prod.snd ⁻¹' D)) = 0 := by
    filter_upwards [localRootKernel_ac_ae P lam hlam, hzero] with ω hac hz
    exact hac hz
  rw [lintegral_congr_ae hae, lintegral_zero]

end HarmonicBalls
