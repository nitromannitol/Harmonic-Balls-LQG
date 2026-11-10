import HarmonicBalls.FirstPass.S8c.LocalObservation

/-! # FIRST-PASS frozen external input for Lemma 8.2 (worker n4, fp-S8c-8-2-local)

One EXTERNAL Prop, the local joint field-measure identification of the rooted comparison in Lemma 8.2
(`lemma:mu_h-doubling-and-harnack`, corrected paper, lines 2151-2220, and [C1] near the origin). It is stated
about the whole-plane GFF `P, hC, hcirc` and its LQG measures only (`μ` of insertion `α₀`, `ν` of insertion `γ`,
and the no-insertion measure `lam`). It mentions no cluster, odometer, harmonic ball or IDLA process.
Its objects are the Draft predicates `IsWholePlaneGFF` and `IsLQGMeasureOfField` and the displayed maps of
`FirstPass/S8c/LocalObservation.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- FIRST-PASS FROZEN. Local joint field-measure identification for Lemma 8.2 (local form, ball about `z`
avoiding `0`, normalised restricted measures). The root law is the normalised restriction `λ|B_1(0) / λ(B_1(0))`
of the no-insertion LQG measure `λ` of the whole-plane GFF, and the statement is domination of its observation
(`localRootObservation μ j`, recentred restriction of the `α₀`-measure `μ` at the root) by the reference
observation (`localReferenceObservation ν j`, `γ`-insertion measure `ν` on `B_{r_j}(0)`, with root `z` Lebesgue
distributed on `localDomain j` and independent of the field).
Source: Duplantier, Miller, Sheffield, arXiv:1409.7055v4, Lemma A.10, p. 184 (whole-plane paragraph, marked
sampling description), local joint form: locator pending (the field marginal is printed; the joint
field-measure form is not). Operator ruling 2026-11-09 17:45 UTC; displayed form in
`docs/campaign/audits/LocalRootedComparisonRepair.md`, section "Actual local observation".
Used by: firstPass_8_2 (through the local reduction in `FirstPass/S8c/`).
Restated (owner n4, 2026-11-09, after the referee verdict in notes/fp-gaps/CHATGPT-truth-new-frozen.md, which
marked the earlier form UNCLEAR): the three a.s. premises give every nonempty open set positive mass under `μ`, `ν`
and `lam`, so each normalised restriction (the root kernel `λ|B_1/λ(B_1)`, the recentred `μ` at the root, the
reference `ν` on `B_{r_j}(0)`) has a positive denominator. Local finiteness (Radon) is already part of
`IsLQGMeasureOfField` through `IsLQGLimit`. The conclusion is domination `≪`, not equality, as the referee requires
for normalised marked laws. Without the positivity premises a degenerate observation (zero measure) would give root
mass that the reference side need not carry. Truth check TRUE (ChatGPT, turn 2, batch file 02:58 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, §6; turn 1 at
02:49 UTC read it as UNCLEAR while the helpers were missing): with the restriction kernel, the local marked-point
comparison gives domination, and almost-sure versions suffice. Both observations use the same B_{r_j/2} mass
normalization: `massNormalize` (HarmonicBalls/FirstPass/S8c/LocalObservation.lean:37) is used in
`localRootObservation` (line 41) and `localReferenceObservation` (line 46). Not checked: the body of
`weightedRestrictionKernel`, which `localRootKernel` (line 51) calls. The answer uses only the stated
normalized-restriction specification: almost surely, the restriction to `localDomain j` is absolutely continuous
with respect to λ_ω restricted there (the exact scalar is unnecessary for domination). Source as the answer gives
it: Duplantier-Miller-Sheffield, arXiv:1409.7055v4, pp. 184-185, Lemma A.10 (whole-plane paragraph, p. 184); HB,
arXiv:2208.11795v3, p. 42, proof of Lemma 8.2, around (8.10); Miller-Sheffield, Imaginary Geometry IV,
arXiv:1302.4738v2, p. 49, Proposition 2.9, (2.8). The normalized measure-valued pushforward statement is a corollary
of these printed comparisons.

Truth check TRUE (ChatGPT Pro chat 219, `notes/fp-gaps/CHATGPT-219-hb-8-2-R9-hL1-hWeyl-PRO.md` §2.1). Not derivable from the
staged unmarked DMS inputs (§3). Derivable from a marked joint `(z, hC, hcirc)` DMS input (§4-§5); phase 2. The existing
marked input `DMSLemmaA10WholePlaneMarked` (`FirstPass/Frozen/S11i.lean:39`) tests `hC` only and carries one circle average
`hcirc ω 1 0`, not the circle profile that `LQGMeasureOfProfileMeasurableFrozen` (`FirstPass/Frozen/S8d.lean:33`) needs
in §5 Step 5, so it does not supply the joint input. -/
def LocalRootedFieldMeasureDomination : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ),
    ∀ hGFF : IsWholePlaneGFF P hC hcirc, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMeasureOfField P γ γ hcirc ν →
    ∀ hlam : IsLQGMeasureOfField P γ 0 hcirc lam,
    (∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U) →
    (∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν ω U) →
    (∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < lam ω U) →
    ∀ j : ℕ, 1 ≤ j →
      ((P ⊗ₘ localRootKernel P lam (hGFF.aemeasurable_lqgMeasure hlam)).restrict
          (Prod.snd ⁻¹' localDomain j)).map (localRootObservation μ j) ≪
        ((volume.restrict (localDomain j)).prod P).map (localReferenceObservation ν j)

/-- RETIRED (derived): proved as `localLQGInsertionWeylOffOrigin_derived` (FirstPass/S8c/WeylOffOriginDerived.lean,
commit 8f3e426), ChatGPT Pro chat 219 §1.3; the derived lemma has no hypotheses. The hWeyl-free versions of the closures
are the `_noWeyl` declarations of FirstPass/Closure/Sec8Weyl.lean (commit 7cd9ede), FirstPass/Closure/NoWeylMain.lean
(commit 4ca8fa1) and FirstPass/Closure/Sec11NoWeyl.lean (commit 7382b13). The original closures are unchanged and still
take `hWeyl` as a binder; not every closure has a hWeyl-free version yet. This statement is unchanged.

FIRST-PASS FROZEN. Weyl relation of the insertion off the origin, used in the local rooted comparison of
Lemma 8.2: almost surely, the no-insertion LQG measure `lam` of the whole-plane GFF satisfies
`lam = |z|^{γ α₀} μ` on the complement of `0`, where `μ` is the LQG measure with insertion `α₀`
(`h = H - α₀ log|·|`, so `μ_h = |z|^{-γ α₀} μ_H` off `0`).
Source: standard LQG insertion and Weyl change of variables (Duplantier-Sheffield, Ann. Probab. 2011;
Duplantier-Miller-Sheffield, arXiv:1409.7055v4); standard; locator pending. Stated as "λ = |·|^{α₀γ} μ off zero"
in notes/fp-gaps/G-8-2.md, section 4. Used by: firstPass_8_2 (through FirstPass/S8c/WeylOffOrigin.lean). Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): the vague
approximation identifies the two measures off 0, with density |z|^{γα₀}. Source as the answer gives it: HB,
arXiv:2208.11795v3, p. 9, (2.6) and Fact 2.1(III); the identity is also printed explicitly on p. 42, proof of Lemma
8.2. -/
def LocalLQGInsertionWeylOffOrigin : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ lam : Ω → Measure ℂ),
    ∀ _hGFF : IsWholePlaneGFF P hC hcirc, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ _hlam : IsLQGMeasureOfField P γ 0 hcirc lam,
    ∀ᵐ ω ∂P, ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s →
      lam ω s = ∫⁻ z in s, ENNReal.ofReal (‖z‖ ^ (γ * α₀)) ∂(μ ω)

/-- FIRST-PASS FROZEN. Birkhoff's pointwise ergodic theorem for bounded measurable functions: for a probability space,
an ergodic measure-preserving map `T` and a measurable `f` with `|f| ≤ 1`, the Cesàro averages of `f ∘ T^[n]` converge
almost surely to `∫ f`. Source: Birkhoff (1931); standard; locator pending (e.g. Walters, An Introduction to Ergodic
Theory, GTM 79, the pointwise ergodic theorem). Used by: firstPass_8_2 (through FirstPass/S8c/Frequency.lean, the phase
tail LocalPhaseTailStep of notes/fp-gaps/G-8-2.md section 3). Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): a bounded
measurable f is integrable, and ergodicity makes its Birkhoff limit the integral. Source as the answer gives it:
Einsiedler-Ward, Ergodic Theory with a view towards Number Theory (draft dated 21 June 2010), p. 44, Theorem 2.30. -/
def BirkhoffPointwiseErgodic : Prop :=
  ∀ (Y : Type u) [MeasurableSpace Y] (ν : MeasureTheory.Measure Y) [MeasureTheory.IsProbabilityMeasure ν]
    (T : Y → Y) (f : Y → ℝ),
    MeasureTheory.MeasurePreserving T ν ν → Ergodic T ν → Measurable f → (∀ y, |f y| ≤ 1) →
    ∀ᵐ y ∂ν, Filter.Tendsto (fun k : ℕ => (∑ n ∈ Finset.range k, f (T^[n] y)) / (k : ℝ)) Filter.atTop
      (nhds (∫ z, f z ∂ν))

end HarmonicBalls
