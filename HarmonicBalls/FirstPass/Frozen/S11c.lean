import HarmonicBalls.Draft.Section11

/-!
# FIRST-PASS FROZEN inputs of Lemmas 11.7 and 11.10 (task fp-S11c-11-7-redo-11-10, worker n1)

Each `Prop` here is EXTERNAL: a general GFF / LQG / measure-theory / potential-theory fact, not a statement about
this paper's clusters, odometers, harmonic balls or IDLA processes. Its docstring gives the source locator, or
"standard; locator pending". Used by the `firstPass_11_10` route in `FirstPass/S11c.lean`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The Weyl shift of an LQG pair `(ν, d)` (a measure and a metric on `ℂ`) by a function `f`: the measure acquires
the density `exp (γ f)` and the metric is the `d`-length weighted metric with weight `exp (ξ f)`, that is
`weylScaling d ξ f` (`Defs/LQGMetric.lean`). Paper Facts 2.1 and 2.2 give this as the transformation of
`(μ_h, D_h)` under `h ↦ h + f`. Caveat: the metric component is real-valued, so `toReal` is applied; the frozen
statement below is used only where the weighted distances are finite. -/
noncomputable def weylShiftPair (γ ξ : ℝ) (f : ℂ → ℝ) (p : Measure ℂ × (ℂ → ℂ → ℝ)) :
    Measure ℂ × (ℂ → ℂ → ℝ) :=
  (p.1.withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))),
    fun u v => (weylScaling p.2 ξ f u v).toReal)

/-- The enlargement `Ŝ` of the dyadic cell `closedDyadicSquare n j k` used in the proof of Lemma 11.10 (paper
line 3010): the closed square with the same centre and side `2^{-n} + 2^{-n-2}`. -/
def enlargedDyadicCell (n j k : ℤ) : Set ℂ :=
  {z : ℂ | |z.re - ((j : ℝ) + 1 / 2) * (2 : ℝ) ^ (-n)| ≤ ((2 : ℝ) ^ (-n) + (2 : ℝ) ^ (-n - 2)) / 2 ∧
    |z.im - ((k : ℝ) + 1 / 2) * (2 : ℝ) ^ (-n)| ≤ ((2 : ℝ) ^ (-n) + (2 : ℝ) ^ (-n - 2)) / 2}

/-- RETIRED (FALSE, ChatGPT truth check 2026-11-09, operator 19:20 UTC: the premise must be the probability of the source
event, not an outer probability on the raw carrier). Superseded by `CameronMartinEventTransferFrozen`. Former FIRST-PASS
FROZEN: Cameron-Martin positivity transfer for the joint law of the LQG measure and LQG metric
(candidate form of the wave-3 ruling, 2026-11-09; the metric component is corrected to `weylScaling`, see
`weylShiftPair`). Let `f` be smooth, compactly supported and zero on the unit circle. If the event that the shifted
pair `weylShiftPair γ ξ f (μ, D)` lies in a measurable set `B` has positive probability, then so does the event that
`(μ, D)` lies in `B`. Measurability of `ω ↦ (μ ω, D ω)` is an explicit hypothesis.
Why it holds: the Weyl scaling of the LQG measure and metric under `h ↦ h + f` (paper Facts 2.1, 2.2) identifies the
pair for `h + f` with `weylShiftPair γ ξ f (μ_h, D_h)`, and the laws of the whole-plane GFF `h` and `h + f` are
mutually absolutely continuous (Cameron-Martin for smooth compactly supported `f` vanishing on the unit circle).
Source: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9 (printed page 49; the cited form
`MillerSheffieldIG4Prop29` in `Proposed/MillerSheffieldIG4.lean` is Hilbert-space level only), with the Weyl scaling
of Duplantier-Sheffield 2011 for the LQG measure and of the LQG metric (paper Facts 2.1, 2.2; locator pending).
Used by: firstPass_11_10. -/
def CameronMartinPositivityTransferFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ) (f : ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    Measurable (fun ω => (μ ω, D ω)) →
    ∀ B : Set (Measure ℂ × (ℂ → ℂ → ℝ)), MeasurableSet B →
      0 < (P.map (fun ω => (μ ω, D ω))) (weylShiftPair γ ξ f ⁻¹' B) →
      0 < (P.map (fun ω => (μ ω, D ω))) B

/-- FIRST-PASS FROZEN. Small internal diameter of the enlarged dyadic cells, simultaneously for all cells of one
level inside a closed dyadic square `S2` disjoint from the unit circle, in inner-probability form.
Why it holds (as printed): each cell has internal diameter tending to zero in probability as the level grows
(the pointwise small-scale continuity of the LQG metric).
FLAG (defect (b) of the Lemma 11.10 proof, paper lines 3010-3016, reported 2026-11-09): the printed step passes from
the pointwise statement to the simultaneous statement over about `4^N` cells by a union bound, which needs a
quantitative tail that the printed statement does not give. This Prop is therefore the printed simultaneous form
and must be ruled on by the operator before it is used as an external input.
Source: Ding-Dubédat-Dunlap-Falconet, Tightness of Liouville first passage percolation for γ < 2 (Publ. IHES 2020),
Lemma 3.19, as cited by paper `dubedat2020weak` (locator pending).
Used by: firstPass_11_10. -/
def DyadicCellDiamSmallFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ S2 : Set ℂ, IsClosedDyadicSquare S2 → Disjoint S2 (sphere 0 1) →
  ∀ ε η : ℝ, 0 < ε → 0 < η →
  ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    ∃ A ⊆ {ω | ∀ j k : ℤ, closedDyadicSquare (N : ℤ) j k ⊆ S2 →
        ∀ u ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2, ∀ v ∈ enlargedDyadicCell (N : ℤ) j k ∩ S2,
          internalMetric (D ω) (enlargedDyadicCell (N : ℤ) j k ∩ S2) u v ≤ ENNReal.ofReal ε},
      MeasurableSet A ∧ ENNReal.ofReal (1 - η) ≤ P A

/-- A closed axis-parallel rectangle `[a₁,a₂] × [b₁,b₂]` in `ℂ` (closed dyadic squares are special cases). -/
def IsClosedRectangle (R : Set ℂ) : Prop :=
  ∃ a₁ a₂ b₁ b₂ : ℝ, a₁ < a₂ ∧ b₁ < b₂ ∧ R = Icc a₁ a₂ ×ℂ Icc b₁ b₂

/-- FIRST-PASS FROZEN. Finite diameter of a compact connected finite union of closed rectangles, for the LQG metric:
almost surely there is a finite bound on the internal distances within the union. (Generalized on 2026-11-09 from
closed dyadic squares to closed rectangles: the exterior set of Lemma 11.10 is a union of rectangles, not of dyadic
squares. The printed text, paper lines 3026-3028, says "a finite union of closed Euclidean squares".)
Why it holds: the metric is finite and continuous on a compact connected union of rectangles (length metric, finite on
compact sets).
Source: Ding-Dubédat-Dunlap-Falconet (Publ. IHES 2020), Lemma 3.9, as cited by paper `dubedat2020weak` in the proof of
Lemma 11.10 (paper lines 3026-3028; locator pending; the exact hypotheses of DDDF20 Lemma 3.9 are unverified).
Used by: firstPass_11_10. -/
def ConnectedSquareUnionDiamFiniteFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ K : Set ℂ, (∃ F : Finset (Set ℂ), (∀ R ∈ F, IsClosedRectangle R) ∧ K = ⋃ R ∈ F, R) → IsConnected K →
  ∀ᵐ ω ∂P, ∃ A : ℝ, ∀ u ∈ K, ∀ v ∈ K, internalMetric (D ω) K u v ≤ ENNReal.ofReal A

/-- FIRST-PASS FROZEN (operator ruling, FIRST PASS wave 4, item n1, 2026-11-09). Field-level measurability of the internal
supremum of the LQG metric over a finite union of closed rectangles: for such a set `K` (in particular a closed dyadic
square, and the rectangles and their unions used in Lemma 11.10), `ω ↦ sup_{u,v ∈ K} D_h(u,v; K)` is measurable.
The operator's wave-4 item covers closed dyadic squares; the extension to finite unions of closed rectangles (the
enlarged pieces `Ŝ ∩ S₂` and the exterior set `K₁`) is requested and flagged for the operator's ruling.
Source: measurability of the LQG metric at field level (paper Fact 2.2 setting; locator pending).
Used by: firstPass_11_10. -/
def LQGMetricSupMeasurableFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ K : Set ℂ, (∃ F : Finset (Set ℂ), (∀ R ∈ F, IsClosedRectangle R) ∧ K = ⋃ R ∈ F, R) →
    AEMeasurable (fun ω => ⨆ u ∈ K, ⨆ v ∈ K, internalMetric (D ω) K u v) P

/-- FIRST-PASS FROZEN (operator ruling, FIRST PASS wave 4, item n1, 2026-11-09). Measurability of the LQG area measure
of a closed dyadic square: `ω ↦ μ_h(S)` is measurable.
Source: locality of the LQG measure, paper Fact 2.1 II (line 407: `μ_h(U)` is a measurable function of `h|_U`), applied to
open neighbourhoods of `S` and continuity from above of the finite measure; locator pending.
Used by: firstPass_11_10. -/
def LQGMeasureSquareMeasurableFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ S : Set ℂ, IsClosedDyadicSquare S → AEMeasurable (fun ω => μ ω S) P

/-- FIRST-PASS FROZEN. The LQG area measure charges every closed dyadic square with nonempty interior, almost surely.
Source: full support of the Gaussian multiplicative chaos measure (Duplantier-Sheffield 2011, Liouville quantum gravity
measure; the paper's introduction, line 138, states that `μ_h` assigns positive mass to open sets); locator pending.
Used by: firstPass_11_10 (through the event `μ_h(S₁) > 0`). -/
def LQGMeasureSquarePositiveFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ S : Set ℂ, IsClosedDyadicSquare S → ∀ᵐ ω ∂P, 0 < μ ω S

/-- FIRST-PASS FROZEN (19:20 UTC truth check: the shifted event is required to be measurable, so that its probability is
that of a source event; the field-level measurabilities are stated almost everywhere (AEMeasurable), since the LQG
objects are defined only almost surely (IsLQGMeasureOfField, IsLQGMetricOfField); wave-4 candidate form, 2026-11-09; supersedes the measurable-`B` form above for Lemma 11.10). Event
form of the Cameron-Martin positivity transfer for the joint event `{sup_{S₂} D_h ≤ c, μ_h(S₁) ≥ C}`. Let `f` be smooth,
compactly supported and zero on the unit circle, and let `(μ, D)` be the LQG measure and metric of the whole-plane GFF,
shifted by `f` through `weylShiftPair` (Weyl scaling, paper Facts 2.1 III and 2.2). If the shifted event has positive
outer probability, then the unshifted event has positive probability. The unshifted event is measurable by the two
measurability items above (hypotheses here).
Why it holds: the shifted pair is the pair of the field `h + f` a.s. (Weyl scaling), and the laws of `h` and `h + f`
are mutually absolutely continuous (Cameron-Martin for `f` smooth, compactly supported, zero on the unit circle).
Source: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9 (printed page 49; Hilbert-space form
in `Proposed/MillerSheffieldIG4.lean`), with the Weyl scaling of paper Facts 2.1 III and 2.2; locator pending.
Used by: firstPass_11_10. -/
def CameronMartinEventTransferFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ) (f : ℂ → ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → (∀ z : ℂ, ‖z‖ = 1 → f z = 0) →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (S₁ S₂ : Set ℂ) (c C : ℝ≥0∞),
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
  IsClosedDyadicSquare S₁ → IsClosedDyadicSquare S₂ →
  AEMeasurable (fun ω => ⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (D ω) S₂ u v) P →
  AEMeasurable (fun ω => μ ω S₁) P →
  NullMeasurableSet {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ c ∧
    C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} P →
  0 < P {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S₂ u v) ≤ c ∧
    C ≤ (weylShiftPair γ ξ f (μ ω, D ω)).1 S₁} →
  0 < P {ω | (⨆ u ∈ S₂, ⨆ v ∈ S₂, internalMetric (D ω) S₂ u v) ≤ c ∧ C ≤ μ ω S₁}

/-- FIRST-PASS FROZEN (operator ruling, FIRST PASS 18:35 UTC, item n1: "the closed-set Weyl comparison for internal metrics
is EXTERNAL (Weyl scaling of the LQG metric): freeze it in the weakest form used"). Weyl comparison of internal metrics on a
closed set. Let `D` be a Euclidean length metric (the LQG metric, paper Fact 2.2 I), let `E` be the Weyl-scaled metric
`E = weylScaling D ξ f` (paper Fact 2.2 III, `D_{h+f}(u,v) = inf_P ∫ e^{ξf(P)} ds_D`), and let `U` be closed with `ξ f ≤ B`
on `U`. Then the internal metric of `E` on `U` is at most `e^B` times the internal metric of `D` on `U`.
Why it holds: a curve in `U` is a competitor, after reparametrization by `D`-arclength, in the infimum defining `weylScaling`
on each sub-arc, so its `E`-length is at most its weighted `D`-length, which is at most `e^B` times its `D`-length (the
weight is at most `e^B` on `U`); the infimum over curves in `U` gives the claim.
Source: paper Fact 2.2 III (corrected copy, lines 441-447) for the full metric; the internal form on closed sets is used in
the printed proof of `prop:mass-diam-gen` (lines 3108-3128, eq:use-weyl) without a separate statement; the repo has the
open-set version `IsEuclideanLengthMetric.internalMetric_weylScaling_le` (Steps/Sec11/WeylAnnulusBounds.lean, hypothesis
`IsOpen U`). Locator pending.
Used by: firstPass_11_10 (through S11c/Shifted.lean). -/
def WeylInternalClosedFrozen : Prop :=
  ∀ (D E : ℂ → ℂ → ℝ) (ξ B : ℝ) (f : ℂ → ℝ) (U : Set ℂ), IsEuclideanLengthMetric D →
    (∀ x y, 0 ≤ E x y) → (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) → IsClosed U →
    (∀ z ∈ U, ξ * f z ≤ B) → ∀ x y, internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D U x y

end HarmonicBalls
