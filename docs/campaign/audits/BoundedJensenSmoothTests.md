# Audit: BoundedJensenSmoothTests (task e51-bounded-jensen-smooth-test-membership)

Owner: q2. File: `HarmonicBalls/Proofs/Potential/BoundedJensenSmoothTests.lean` (168 lines, new).
Scope: bounded-test ingredient of the bounded Jensen representative lemma (steps3:230-315). Not the Fatou or localization steps.

## Statement (exact binders, lines 57-61)

```
theorem HarmonicBalls.mem_boundedSubharmonicBallTestClass_of_smooth_compactSupport
    (S : Set ℂ) (z : ℂ) (hS : IsOpen S) (hSb : Bornology.IsBounded S) (_hz : z ∈ S)
    (F : ℂ → ℝ) (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hsub : ∀ x ∈ S, 0 ≤ Laplacian.laplacian F x) :
    F ∈ boundedSubharmonicBallTestClass S z
```

Elaboration choices (operator to confirm):
- The task's `ContDiff Real top F` is read as C^∞, the project's smooth index `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)` (the `IsTestFunction` convention, `Defs/Laplacian.lean:47-48`). The name says "smooth". A C^ω hypothesis (`⊤ : WithTop ℕ∞`) would imply C^∞ by `ContDiff.of_le`, so the stated version is at least as strong.
- `_hz : z ∈ S` is kept to match the stated hypotheses but is not used: the class conditions at the pole `z` hold for every `z`.

## Witnesses (the definition is `Audit/GreenSubharmonicTestClass.lean:14-18`)

- `O = ball 0 (R₀ + 1)`, with `closure S ∪ tsupport F ⊆ closedBall 0 R₀` from `Bornology.IsBounded.subset_closedBall`. `O` is open and bounded, and `closure S ⊆ O`.
- `K = closedBall 0 R₀`, compact, `K ⊆ O`.
- `q = 0`, harmonic on `O` by `InnerProductSpace.harmonicOnNhd_const` (`Mathlib/Analysis/InnerProductSpace/Harmonic/Basic.lean:86`).
- `ν₁ = volume.withDensity (ofReal ∘ a)`, `a y = max (-ΔF y) 0` (the density of `(-ΔF)₊ dx`).
- `ν₂ = volume.withDensity (ofReal ∘ b)`, `b y = max (ΔF y) 0` (the density of `(ΔF)₊ dx`).
- Checks: `ν₁ S = 0` (since `ΔF ≥ 0` on `S`, so `a = 0` there); `ν₁ Kᶜ = ν₂ Kᶜ = 0` (since `ΔF = 0` off `tsupport F ⊆ K`); `ν₂ {z} = 0` (absolute continuity, `measure_singleton`); both finite (`isFiniteMeasure_withDensity_ofReal`); `Integrable (greenFunction O z) ν₂` (`integrable_withDensity_iff` and `integrable_greenFunction_mul_bdd`).

## Global representation (every point of `ℂ`, not a.e.)

- `integral_greenFunction_mul_laplacian_eq` (lines 33-45): `∫ G_O(x,y) ΔF(y) dy = -F(x)` for all `x ∈ ℂ`. For `x ∈ O` it is `hasLaplacian_greenFunction_bounded_domain` (`Proofs/Potential/GeneralDomainGreenLaplacian.lean:15-17`, `HasLaplacian (greenFunction V z) 0 (dirac z) V`) applied to the test function `F`. The definition is `Defs/Laplacian.lean:72-75`. For `x ∉ O`, `greenFunction O x · = 0` (`Defs/Green.lean:70-74`) and `F x = 0`.
- `hpot₁`, `hpot₂` (Step 6): `greenPotential O ν x = ∫ G_O(x,y) · (density) dy`, via `integral_withDensity_eq_integral_toReal_smul₀` (`Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean:310`).
- `hdiff` (Step 7): `greenPotential O ν₁ x - greenPotential O ν₂ x = -∫ G_O(x,y) ΔF(y) dy`, via `max_neg_sub_max_eq_neg` (lines 48-50): `(-t)₊ - t₊ = -t`.
- `hrep`: `F = 0 + greenPotential O ν₁ - greenPotential O ν₂` as functions, which closes the membership.

## Written-proof audit (`mcrt` notes/wpn-steps3/steps3.tex:261-280`; `AUDIT-steps3.md:25-34`)

- `α_n(S) = 0` holds, as written. `β` has no atoms (absolute continuity). Its Green kernel at `z` is integrable.
- The AUDIT note (`AUDIT-steps3.md:260-279`) asked to replace "smooth source measures" by "source measures with bounded continuous densities". The formal densities are continuous with compact support, which is all the proof uses.
- The written disk-Green-formula step is replaced by the distributional identity for `G_O(x,·)` on an arbitrary bounded open `O`. That needs no disk-specific formula. The conclusion is global equality on `ℂ`.
- No gap was found. No new mathematics was added, no literature input was admitted, and no hypothesis was added.

## Reuse search and duplicates

- Project grep for `boundedSubharmonicBallTestClass`: the definition and lemmas in `Audit/GreenSubharmonicTestClass.lean`, and uses in `Proofs/Potential/BoundedSubharmonicRepresentatives.lean` (read-only). None is a smooth-compact-support membership.
- Grep for the new names across `HarmonicBalls` (excluding this file): no consumers and no duplicates.
- Mathlib: the Green-function lemmas are project-internal. The measure lemmas come from Mathlib.

## Import closure, consumers, credit

- Direct imports: `Audit/GreenSubharmonicTestClass`, `Proofs/Potential/GeneralDomainGreenLaplacian`, `Proofs/Potential/BoundedDensityGreenContinuity`, `Proofs/Potential/Fundamental`.
- Import closure: 354 `HarmonicBalls` modules including self, none missing (script walk of `^import HarmonicBalls` lines). `HarmonicBalls.Proposed.Birkhoff` and `HarmonicBalls.Proposed.LQG` enter through existing imports only. The new proofs do not reference them, and they stay pending operator source-check. 14 closure files mention Bonanno or Lattice-Probability.
- Consumers: none yet. The unrestricted consumer upgrade at `Audit/GreenSubharmonicTestClass.lean:54-64` is not changed, because that file is not owned by this task.
- Credit: the module docstring credits Leonardo Bonanno through the pinned Lattice-Probability (lean-v4.35) port, with the wording of `BoundedDensityGreenStability.lean:25-30`.

## Checks

- `lc`: CHECK OK, with `-DwarningAsError=true`.
- `lb HarmonicBalls.Proofs.Potential.BoundedJensenSmoothTests`: BUILD OK.
- `#print axioms` for the main theorem and both helpers: `[propext, Classical.choice, Quot.sound]` (scratch file `/tmp/q2-ax/AxE51.lean`, not committed).
- Raw scan of the file for `sorry`, `axiom`, `admit`, `native_decide`, `unsafe`, `extern`, `implemented_by`, `opaque`, `maxHeartbeats`, `maxRecDepth`, `set_option`, `kernel`, `decide`: 0 hits, including comments.

## Not done here

- Fatou and localization for the bounded Jensen representative lemma (steps3:281-315).
- The consumer upgrade at `Audit/GreenSubharmonicTestClass.lean:54-64`.
