import HarmonicBalls.Proposed.LQG

/-!
# Frozen inputs for Proposition 11.9

FROZEN inputs for `firstPass_11_9` (paper `prop:mass-diam-gen`, corrected draft lines 3018-3137). Each is a `def ... : Prop` (never an axiom). Reused, not re-frozen: `LQGMeasureWeylScaling`
(Proposed/LQG.lean, Fact 2.1 III) and `LQGMetricFieldAxioms` (Proposed/LQG.lean, Fact 2.2 I-IV for `h = h^ℂ - α₀ log|·|`,
including the Weyl identity III: `weylScaling (𝔇 (hC ω)) ξ (f - α₀ log) = weylScaling (D_h ω) ξ f`).
-/

universe u

namespace HarmonicBalls

open MeasureTheory
open scoped ENNReal

/-- FROZEN. Plane topology (standard; locator pending). For a connected open `V ⊆ ℂ` and a compact convex
`K ⊆ V`, the set `V \ K` is preconnected. Source: Alexander duality in `S²`: the Čech `H¹` of the complement of `V` and
of `K` vanish, so the complement of their union is connected (for `K` a closed dyadic square this is the connectedness
of `V \ S₂` used in the paper, proof of `prop:mass-diam-gen`, line 3120). Used by: firstPass_11_9. Truth check TRUE: a compact
convex set contained in an open connected plane domain does not disconnect that domain. Source: consequence of Alexander duality, Hatcher, Algebraic Topology (2002), p. 255, Corollary 3.45, with the
Čech-cohomology extension on pp. 256-257. -/
def PlaneDomainMinusConvexCompactPreconnectedFrozen : Prop :=
  ∀ V K : Set ℂ, IsOpen V → IsConnected V → IsCompact K → Convex ℝ K → K ⊆ V → IsPreconnected (V \ K)

/-- FROZEN. Fact 2.2 I for the field `h + g = h^ℂ + g - α₀ log|·|` with `g` continuous: a.s. the Weyl-scaled
metric `e^{ξ g} · D_h` is finite and a length metric inducing the Euclidean topology. Source: Bou-Rabee-Gwynne
(arXiv:2208.11795) Fact 2.2 I (lines 432-457) applied to `h + f` as in Fact 2.2 III (line 445); Gwynne-Miller 2021
(`gwynne2021existence` in the paper bibliography; arXiv locator pending) Section 1.2 p. 6; Dubedat-Falconet-Gwynne-Pfeffer-Sun 2020 (arXiv:1905.00380)
Theorem 1.10 p. 10 and Proposition 3.17 p. 43 for the log singularity. Used by: firstPass_11_9. -/
def LQGMetricContinuousShiftFactI : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ g : ℂ → ℝ, Continuous g →
      ∀ᵐ ω ∂P, (∀ u v, weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v < ⊤) ∧
        IsEuclideanLengthMetric fun u v =>
          (weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v).toReal

/-- FROZEN. Fact 2.2 II (locality) for the field `h + g` with `g` continuous: for each deterministic open `U`,
the internal metric of the Weyl-scaled metric on `U` is a.s. equal to a function `G` that is measurable for the
pairing σ-algebra of `hC` on `U` (the σ-algebra of `h + g` on `U` equals that of `h` on `U`, since `g` is deterministic).
Source: Bou-Rabee-Gwynne (arXiv:2208.11795) Fact 2.2 II (line 441), applied to `h + f` (Fact 2.2 III, line 445);
Gwynne-Miller 2021 Section 1.2 p. 6 (locator pending). Truth check TRUE: the decoder is chosen after the metric and equality is almost sure;
locality follows from the base locality axiom for the unweighted metric `𝔇(h^ℂ)` by a Borel weighted-path construction, with
the `.toReal` convention checked at the insertion (§3.3). Sources: Gwynne-Miller Section 1.2, axiom II
(§3.5); Bou-Rabee-Gwynne Fact 2.2 I–IV, printed p. 10 in v3 (the p. 9 reference is corrected). Used by: firstPass_11_9. -/
def LQGMetricContinuousShiftLocality : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ g : ℂ → ℝ, Continuous g → ∀ U : Set ℂ, IsOpen U →
      ∃ G : Ω → ℂ → ℂ → ℝ≥0∞, (∀ z w, Measurable[pairingSigmaAlgebra hC U] fun ω => G ω z w) ∧
        ∀ᵐ ω ∂P, ∀ z ∈ U, ∀ w ∈ U,
          internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun x => g x - α₀ * Real.log ‖x‖) u v).toReal) U z w
            = G ω z w

/-- FROZEN. Cameron-Martin quasi-invariance of the whole-plane GFF on distribution-level events (standard;
locator: Miller-Sheffield Imaginary Geometry, Proposition 2.9 (paper line 3106 cites it as miller2017imaginary) for the Cameron-Martin shift
`h ↦ h + g` with `g` in the Cameron-Martin space; the whole-plane GFF normalised by its unit-circle average, so the shift
must have zero unit-circle average). For smooth (`C^∞`, so in the Dirichlet/Cameron-Martin space) compactly supported `g` with zero unit-circle average, the laws of `hC`
and `hC + g` on the distribution σ-algebra are mutually absolutely continuous: a measurable set of fields is null for
`hC` iff it is null for `hC + g`. Version stated explicitly. Truth check: UNCLEAR for the unrestricted distribution σ-algebra; Truth check TRUE for the version below (row `CameronMartinGFFMutualAbsCont`: the σ-algebra observes only test pairings). The events are the sets of the σ-algebra
`distributionMeasurableSpace` generated by the test pairings `T ↦ T φ` (genuine test-pairing events, no outer probability on
the raw carrier); each such set depends on countably many pairings, and on those the Gaussian laws are equivalent by
Feldman-Hajek, the mean shift `φ ↦ ∫ g φ` lying in the Cameron-Martin space of the normalised GFF. Used by: firstPass_11_9 (transfer of the positive-probability event from the shifted field
`h~ = h - (φ/ξ) log(2A/ε)` back to `h`, paper line 3131, "since the laws of h and h~ are mutually absolutely continuous"). -/
def CameronMartinGFFMutualAbsCont : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (g : ℂ → ℝ), IsWholePlaneGFF P hC hcirc → ContDiff ℝ (⊤ : ℕ∞) g →
    HasCompactSupport g → Real.circleAverage g 0 1 = 0 →
    ∀ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B →
      (P ((fun ω => hC ω) ⁻¹' B) = 0 ↔ P ((fun ω => addFunPairing (hC ω) g) ⁻¹' B) = 0)

/-- DERIVED INTERFACE. "It is a consequence of Weyl
scaling and the log-singular extension, not a separately printed theorem with this exact type."
FROZEN. Composition rule of Weyl scalings for the log-singular LQG metric (paper Fact 2.2 III, line 445:
`D_{h+f} = e^{ξ f} · D_h` for continuous `f`, applied with `h = h^ℂ - α₀ log|·|`; Gwynne-Miller 2021, Section 1.2 p. 6 and
Remark 1.5 p. 8; Dubedat-Falconet-Gwynne-Pfeffer-Sun 2020, p. 9). It identifies the metric of the distribution `h^ℂ + g - α₀ log|·|`
(the Defs convention `weylScaling (𝔇 ·) ξ (-α₀ log|·|)`) with the Weyl scaling of the metric of `h`, almost surely.
Used by: firstPass_11_9 (the Weyl comparison `internalMetric_weylScaling_le` for the shifted metric, paper line 3127). Truth check TRUE: a
continuous first Weyl weight permits arclength substitution and multiplication of weights, including the logarithmic
second weight. Source: consequence of Gwynne-Miller, arXiv:1905.00383v3, p. 6, Axiom III,
(1.8), and p. 8, Remark 1.5. -/
def WeylScalingCompositionFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
    ∀ g : ℂ → ℝ, Continuous g →
      ∀ᵐ ω ∂P, ∀ x y : ℂ,
        weylScaling (𝔇 (addFunPairing (hC ω) g)) ξ (fun z => -α₀ * Real.log ‖z‖) x y =
          weylScaling (𝔇 (hC ω)) ξ (fun z => g z - α₀ * Real.log ‖z‖) x y

/-- RETIRED (FALSE, use LQGInternalMetricWeylAeMeasurableFrozen). FROZEN. Field-level measurability of the Weyl-scaled internal metric, uniform form (standard; locator
pending). For every LQG metric `𝔇` (`IsLQGMetric`, Weyl exponent `ξ`), an open set `W` and fixed `q q' : ℂ`, the map
`T ↦ D^W_T(q, q')` is measurable for the σ-algebra of pairings, where `D_T = e^{-ξ α₀ log|·|} · 𝔇 T` and `D^W_T` is its
internal metric on `W`. Source: measurability of `h ↦ D_h` (Gwynne-Miller 2021, Section 1.2, p. 6; locator pending), transported
to the internal metric on `W`. Field level, EXTERNAL. Used by:
FirstPass/S11e/CertMeasurable.lean (`measurableSet_certificate_certMetricOn`, line 38). Not used by firstPass_11_9, which uses
the weaker a.s. form `LQGInternalMetricWeylAeMeasurableFrozen` below. Truth check FALSE: measurability of every fixed
evaluation `T ↦ 𝔇 T z w` does not give measurability of the displayed path operation on the entire raw carrier; explicit
counterexample preserving every field of `IsLQGMetric`. Minimal correction: `LQGInternalMetricWeylAeMeasurableFrozen`
below, whose order `∀ 𝔇, ∃ Φ, ∀ f, a.s.` is marked as correct. -/
def LQGInternalMetricWeylMeasurableFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 → ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ,
    Measurable[distributionMeasurableSpace] fun T : (ℂ → ℝ) → ℝ =>
      internalMetric (fun u v => (weylScaling (𝔇 T) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) W q q'

/-- DERIVED INTERFACE. "Field-level measurable
factorization of the Weyl-scaled internal metric is not the literal statement of Axiom II; it requires a version/factorization argument."
FROZEN. Field-level measurable version of the Weyl-scaled internal metric (standard; locator pending). For an
LQG metric `𝔇` (`IsLQGMetric`, Weyl exponent `ξ`) of a whole-plane GFF carrier `(Ω, P, hC, hcirc)`, an open set `W`
and fixed `q q' : ℂ`, there is a measurable functional `Φ` on distributions (for the σ-algebra of pairings) with
`Φ (h^ℂ + f) = D^W(q, q')` almost surely for every continuous `f`, where `D = e^{-ξ α₀ log|·|} · 𝔇(h^ℂ + f)` is the metric
of `h^ℂ + f - α₀ log|·|` and `D^W` its internal metric on `W`. Only this a.s. form is claimed: the infimum over paths defining
`D^W` need not be measurable as a function of the distribution off the support of the carrier. Source: measurability of
`h ↦ D_h` (Gwynne-Miller 2021, Section 1.2, p. 6; locator pending), with the internal metric on an open set as in Fact 2.2 I
(Bou-Rabee-Gwynne arXiv:2208.11795, p. 9, lines 432-457). Field-level measurability is
EXTERNAL and is frozen at field level. Truth check TRUE for this a.s. form (row `LQGInternalMetricWeylAeMeasurableFrozen`). The plain-`Measurable` version is FALSE (row `LQGInternalMetricWeylMeasurableFrozen`), so the a.s. form is the one stated here.
Truth check TRUE: reconstruct the
continuous base metric from countably many evaluations; radial Weyl weighting and internalization on an open set admit a Borel
construction using compact families of rectifiable paths; this supplies one `Φ` for every fixed continuous shift.
Used by: firstPass_11_9 (the Cameron-Martin transfer event, paper line 3131). -/
def LQGInternalMetricWeylAeMeasurableFrozen : Prop :=
  ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMetric γ ξ 𝔇 →
    ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ, ∃ Φ : ((ℂ → ℝ) → ℝ) → ℝ≥0∞,
      Measurable[distributionMeasurableSpace] Φ ∧
      ∀ f : ℂ → ℝ, Continuous f → ∀ᵐ ω ∂P,
        Φ (addFunPairing (hC ω) f) = internalMetric (fun u v =>
          (weylScaling (𝔇 (addFunPairing (hC ω) f)) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal) W q q'

/-- DERIVED INTERFACE. "a measurable functional
representing the mass on a closed set is a consequence of local GMC construction and Weyl scaling, not a verbatim cited theorem."
FROZEN. Field-level measurability of the LQG mass of a closed set (standard; locator pending). For a
whole-plane GFF `hC` with LQG measure `μ` (`IsLQGMeasureOfField`) and a closed set `S`, there is a measurable functional
`F` on distributions such that `F (h^ℂ + f) = μ(S)` almost surely, for every continuous `f` vanishing on `S`. Source: `μ` is
the vague limit of the regularized measures (Duplantier-Sheffield 2011, arXiv:0808.1560v2, Section 3; Bou-Rabee-Gwynne
arXiv:2208.11795 Fact 2.1 III, p. 9, line 418, `LQGMeasureWeylScaling`: `μ_{h+f} = e^{γ f} μ_h`, which gives
`μ_{h+f}(S) = μ_h(S)` when `f = 0` on `S`). Truth check TRUE: one measurable decoder built from countably many
circle-average pairings (sections 2.1-2.3, including every continuous shift), the measure decoded from its defining limit (section 2.4).
Used by: firstPass_11_9 (mass identity `M(h^ℂ + g) = M(h^ℂ)` for the shift `g`
vanishing on `S₁`, paper line 3131). Truth check TRUE: a single decoder can be built before quantifying over the continuous shifts, from countably many circle-average pairings
(§2.1–2.3), and the measure is decoded from its defining limit (§2.4). Sources: Bou-Rabee-Gwynne
eq. (2.6), printed p. 9 (measure construction); Duplantier-Sheffield Proposition 1.1, printed p. 5 (a.s. convergence along
powers of two, including deterministic continuous additive functions), and Proposition 3.1, printed p. 17. -/
def LQGMassFunctionalMeasurableFrozen : Prop :=
  ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → 0 < γ → γ < 2 → α₀ < lqgQ γ → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ S : Set ℂ, IsClosed S → ∃ F : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] F ∧
      ∀ f : ℂ → ℝ, Continuous f → (∀ x ∈ S, f x = 0) →
        ∀ᵐ ω ∂P, F (addFunPairing (hC ω) f) = μ ω S

end HarmonicBalls
