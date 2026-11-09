# Audit: BoundedJensenPotentialIntegrability (task e51, Fatou step of the bounded Jensen argument)

Owned: `HarmonicBalls/Proofs/Potential/BoundedJensenPotentialIntegrability.lean` (new, 172+ lines, namespace
`HarmonicBalls.BoundedJensenFatou`), and this file. Status: `lc` OK, `lb` BUILD OK on the final version.

## Source
- steps3 Section 1, proof of `lem:bounded-jensen-representatives` (tex lines 230-315; sha256 d34cf930...).
- Approximants `u_{2,n}` (246-259); smooth witnesses `F_n = -chi u_{2,n}` (260-280); sub-mean for `F_n` (281-285);
  Fatou and the Jensen bound `eq:potential-jensen` (286-290); finiteness a.e. and atoms (291-298).
- `eq:potential-localization` (tex 214) is used at tex 300 (not formalized; see B2).

## Declarations
1. `jensen_fatou_of_common_lower_bound` (generic; Mathlib-level, no Green function).
   Binders: `{μ : Measure ℂ} {S : Set ℂ} {z : ℂ} {c L : ℝ} {u : ℕ → ℂ → ℝ} {V : ℂ → ℝ≥0∞}`,
   `(hS : MeasurableSet S) (hμS : μ S ≠ ⊤) (hz : z ∈ S) (hVm : AEMeasurable V (μ.restrict S))`,
   `(hmeas : ∀ n, Measurable (u n)) (hint : ∀ n, IntegrableOn (u n) S μ)`,
   `(hlb : ∀ n, ∀ x ∈ S, -c ≤ u n x)`, `(hsub : ∀ n, ∫ x in S, u n x ∂μ ≤ μ.real S * u n z)`,
   `(hpole : Tendsto (fun n => u n z) atTop (𝓝 L))`,
   `(hV : ∀ x ∈ S, V x ≤ liminf (fun n => ENNReal.ofReal (u n x + c)) atTop)`.
   Conclusions: (i) `∫⁻ x in S, V x ∂μ ≤ ofReal ((L + c) * μ.real S)`; (ii) `∀ᵐ x ∂(μ.restrict S), V x < ⊤`;
   (iii) `Integrable (fun x => (V x).toReal) (μ.restrict S)`; (iv) `∫ x in S, ((V x).toReal - c) ∂μ ≤ L * μ.real S`.
   Proof: Fatou (`lintegral_liminf_le`, Mathlib `Integral/Lebesgue/Add.lean:233`) for `ofReal (u n + c)`; the sub-mean
   bound through `ofReal_integral_eq_lintegral_ofReal`; the pole limit; `ae_lt_top'`,
   `integrable_toReal_of_lintegral_ne_top`, `integral_toReal`. `-c ≤ L` follows from `hlb` at `z` (`ge_of_tendsto'`).
   The name is generic: it is not the bounded representative theorem.
2. `greenPotential_jensen_of_bounded_witness` (bounded `O`).
   Binders: `(hJ : ∀ F ∈ boundedSubharmonicBallTestClass S z, HasSubMeanValueProperty μ S z F)`,
   `{O K : Set ℂ} (hO : IsOpen O) (hOb : Bornology.IsBounded O) (hSO : closure S ⊆ O) (hK : IsCompact K) (hKO : K ⊆ O)`,
   `{ν : Measure ℂ} [IsFiniteMeasure ν] (hνK : ν Kᶜ = 0) (hνz : ν {z} = 0) (hνi : Integrable (greenFunction O z) ν)`.
   Conclusion: `IntegrableOn (greenPotential O ν) S μ ∧ ∫ x in S, greenPotential O ν x ∂μ ≤ μ.real S * greenPotential O ν z`.
   Proof: the witness `(O, K, 0, ν, 0)` puts `-greenPotential O ν` in `boundedSubharmonicBallTestClass S z`
   (`InnerProductSpace.harmonicOnNhd_const`; `greenPotential O 0 = 0`); then `hJ` and `integral_neg`.
   This covers the Bochner potential only. No approximation is used, because for bounded `O` the test class is exact.
3. `greenPotential_eq_toReal_of_classical_lt_top` (pointwise, bounded `O`).
   Binders: `(hO : IsOpen O) (hOb : IsBounded O) {ν : Measure ℂ} {x : ℂ} (hx : ∫⁻ y, greenKernelExtended O x y ∂ν < ⊤)`.
   Conclusion: `ν {x} = 0 ∧ Integrable (greenFunction O x) ν ∧ greenPotential O ν x = (∫⁻ y, greenKernelExtended O x y ∂ν).toReal`.
   Proof: the diagonal value `⊤` forces `ν {x} = 0`; `measurable_greenFunction_uncurry` gives measurability;
   `greenFunction_nonneg` and `hasFiniteIntegral_iff_ofReal` give integrability; then `lintegral_greenKernelExtended_eq`.

## Conventions (checked against the definitions)
- `HasSubMeanValueProperty μ Λ z f := IntegrableOn f Λ μ ∧ f z * μ.real Λ ≤ ∫_Λ f` (Draft/Section4.lean:44).
- `greenPotential O μ x = ∫ y, greenFunction O x y ∂μ` (Defs/Green.lean:89): Bochner, value 0 where `y ↦ G_O(x,y)` is not
  integrable. `greenFunction` is 0 on the diagonal and off `O` (Defs/Green.lean:70).
- `greenKernelExtended O x y = if y = x then ⊤ else ofReal (G_O(x,y))` (GreenPotentialExceptionalSet.lean:19).
  For bounded `O`, `G_O ≥ 0` (`greenFunction_nonneg`, Defs/Green.lean:134).
- The ℝ≥0∞ kernel is restricted to bounded `O` in lemma 3. For unbounded `O` the Lean `G_O` need not be nonnegative (the
  greatest-harmonic-minorant definition does not guarantee it), so `ofReal` would discard negative values. The
  classical potential for unbounded `O` is not treated here.

## Imports and consumers
- Direct imports: `Audit/GreenSubharmonicTestClass`, `Defs/Green`, `Proofs/Potential/BoundedDomainGreenMeasurability`,
  `Proofs/Potential/GreenPotentialExceptionalSet`.
- Transitive closure: 316 HB modules (computed from the `import` lines). It includes Draft.Section1-9, SectionA, Audit
  modules, and the existing imports `Proposed/Birkhoff` and `Proposed/LQG`. These two Proposed modules are reached only
  through existing imports. They are not used as hypotheses and remain pending operator source-check. External: 0.
- Consumers: none yet (no HB file imports the new module).
- Credit: Leonardo Bonanno's work, through the pinned Lattice-Probability (lean-v4.35) port, is in the closure. The module
  docstring credits it.

## Checks
- `lc`: CHECK OK (warnings as errors). `lb`: BUILD OK.
- Printed axioms (scratch `/tmp/q2-ax/AxE51.lean`, not committed): all three declarations depend on
  `[propext, Classical.choice, Quot.sound]` only.
- Raw token scan (sorry, axiom, admit, native_decide, unsafe, extern, implemented_by, maxHeartbeats, set_option,
  ofReduceBool, opaque, #exit, initialize, csimp, decide): 0 hits.
- No Proposed or External input, no conclusion-as-hypothesis, no weakened statement.

## Not proved: exact blockers
- **B1 (smooth superharmonic approximants of the classical potential; bounded `O`).** Feeding `jensen_fatou_of_common_lower_bound`
  needs `u : ℕ → ℂ → ℝ` with: measurable and `IntegrableOn` on `S`; a constant `c` with `-c ≤ u n x` on `S`; each `-chi * u n`
  in `boundedSubharmonicBallTestClass S z` (via `mem_boundedSubharmonicBallTestClass_of_smooth_compactSupport`,
  BoundedJensenSmoothTests.lean:57, which needs `ContDiff ℝ ∞`, compact support, and `0 ≤ Δ` on `S`); `Tendsto (u n z)` to
  `greenPotential O ν z`; and `V x ≤ liminf ofReal (u n x + c)` with `V x = ∫⁻ greenKernelExtended O x y ∂ν`. Missing:
  (a) smoothness and `Δ(u n) ≤ 0` on `S` for `u n = greenPotential O ν ⋆ φ_n`. The Green identity
      `integral_greenFunction_mul_laplacian_eq` (BoundedJensenSmoothTests.lean:33) covers bounded `O`, and
      `laplacian_convolution_left` (Sec6/LaplacianConvolution.lean:44) needs local integrability. Not assembled.
  (b) the pole upper bound `limsup u n z ≤ greenPotential O ν z`. This needs the super-mean property of `G_O(·, y)` under radial
      mollifiers. Not located. Nearest: `harmonicOnNhd_greatestHarmonicMinorant_newtonKernel`
      (Proofs/Sec5/GeneralDomainInteriorGreen.lean:12) and `greenFunction_circleAverage_pole`
      (Proofs/Potential/FiniteDiscGreenReciprocity.lean:587), which is for discs.
  (c) the lower bound `liminf u n x ≥ V x` on `S` (lower semicontinuity). This needs `G_O(·,y) → +∞` at `y` for general bounded
      `O`. Not located. Only the ball version `tendsto_greenFunction_ball_pole` (Proofs/Sec8/GreenKernelContinuity.lean:18) exists.
  The mollification providers do not suffice. `exists_compactlySupported_smooth_subharmonic_approximation`
  (Proofs/Sec6/LaplacianConvolution.lean:117) and `exists_local_mollification` (Proofs/Sec6/LocalMollification.lean:49)
  require continuity of the function, and the potential of `ν` is singular at atoms.
- **B2 (unbounded `O`, the full witness).** Localization needs a bounded open `V` with `closure S ∪ K ⊆ V`,
  `closure V ⊆ O`, `G_O(z,·) - G_V(z,·)` harmonic on `V` (or its `ν`-integrated form), and `G_V(z,·) ∈ L¹(ν)`.
  Only the ball comparison exists (`exists_harmonicOnNhd_greenFunction_difference`, Proofs/Sec5/GeneralDomainInteriorGreen.lean:39,
  for `U ⊆ ball 0 r`). Source: tex 214 (`eq:potential-localization`), used at tex 300.
- **B3 (a.e. agreement).** Given finiteness a.e. from B1, `greenPotential_eq_toReal_of_classical_lt_top` gives
  agreement at each point. Without B1 the a.e. claim is not supported.

## Observations for the operator
- The Lean Bochner potential has junk value 0 where `G(x,·)` is not `ν`-integrable, and the Lean diagonal value of
  `greenFunction` is 0, not `-∞`. So `greenPotential_jensen_of_bounded_witness` alone cannot see where the classical
  potential is `⊤`. That is why B1 is needed.
- For `λ = ν = δ_p` (`p ∈ S`): the test `-G(·, p)` gives the junk value 0 at `p`, so it does not refute this case. The
  hypothesis excludes it through other bounded tests, for example `-G(·, w)` with `w` near `p`. This is a remark about the
  hypothesis, not a formal result.
- No statement in this file asserts a conclusion as a hypothesis. No frozen file was edited.

## Decisions to confirm
- The generic Fatou step takes `Tendsto` at the pole and a `liminf` lower bound on `S`, rather than full convergence
  everywhere (the latter is not available without B1).
- The classical potential is `ℝ≥0∞`-valued (`greenKernelExtended`), restricted to bounded `O`.
- `μ S ≠ ⊤` is assumed in the generic step (the consumer has `0 < λ(S) < ∞`).
