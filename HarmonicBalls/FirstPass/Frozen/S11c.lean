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
Attribution (operator note 23:32 UTC; statement audit `notes/fp-gaps/CHATGPT-11-7-11-10-statement-audit.md`, section 2.C): Dubédat-Falconet-Gwynne-Pfeffer-Sun, *Weak LQG metrics and Liouville first passage percolation*, arXiv:1905.00380v2. Quantitative locators: Proposition 3.10 (p. 34, internal square-diameter moments up to the boundary); Lemmas 3.19-3.20 (pp. 45-46, quantitative and simultaneous small-square estimates); Proposition 3.17 (pp. 43-44, admissible logarithmic singularity); equations (3.63) (failure tail) and (3.67) (simultaneous control). The simultaneous statement over the dyadic cells of level N is supplied by (3.63) and (3.67), not by a bare union bound. Source as cited by paper `dubedat2020weak` in the proof of Lemma 11.10 (paper lines 3010-3016). Used by: firstPass_11_10. Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): the axioms
force ξ > 0, and quantitative square estimates and summable insertion bounds give the simultaneous inner-probability
statement. Source as the answer gives it: consequence of DFGPS, arXiv:1905.00380v2, p. 34, Proposition 3.10; pp.
43-44, Proposition 3.17; pp. 45-46, Lemmas 3.19-3.20, (3.63), (3.67). -/
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
Justification (operator note 23:32 UTC; statement audit section 2.C-2.D): internal boundary estimates, Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.10 (p. 34) and Proposition 3.17 (pp. 43-44), together with the rectangle and singularity reductions: finite square coverings away from 0, and summable dyadic shell bounds near 0 where ξ(Q_γ - α₀) > 0. Ambient metric continuity alone does not justify this statement. Source as cited by paper `dubedat2020weak` in the proof of Lemma 11.10 (paper lines 3026-3028); the exact hypotheses of Ding-Dubédat-Dunlap-Falconet, Lemma 3.9 remain unverified. Used by: firstPass_11_10. Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): with
strictly positive rectangle side lengths, internal boundary estimates and the finite connected intersection graph
give finite diameter. Source as the answer gives it: rectangle/closure and singularity consequence of DFGPS,
arXiv:1905.00380v2, p. 34, Proposition 3.10, (3.26); pp. 43-44, Proposition 3.17. -/
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
Source: measurability of the LQG metric at field level (paper Fact 2.2 setting; locator (CHATGPT-frozen-locators.md): no exact source; standard via GM 1.2 and compact-path coding).
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
open neighbourhoods of `S` and continuity from above of the finite measure; locator (CHATGPT-frozen-locators.md): DS Proposition 1.1.
Used by: firstPass_11_10. -/
def LQGMeasureSquareMeasurableFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ S : Set ℂ, IsClosedDyadicSquare S → AEMeasurable (fun ω => μ ω S) P

/-- FIRST-PASS FROZEN. The LQG area measure charges every closed dyadic square with nonempty interior, almost surely.
Source: full support of the Gaussian multiplicative chaos measure (Duplantier-Sheffield 2011, Liouville quantum gravity
measure; the paper's introduction, line 138, states that `μ_h` assigns positive mass to open sets); locator (CHATGPT-frozen-locators.md): RV Theorem 2.12.
Used by: firstPass_11_10 (through the event `μ_h(S₁) > 0`). Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): every such
dyadic square contains an open ball away from 0, where the subcritical chaos measure has positive mass. Source as
the answer gives it: Rhodes-Vargas, arXiv:1305.6221v1, p. 11, Theorem 2.12; full support is also stated in HB
arXiv:2208.11795v3, §1.2, p. 3. -/
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
in `Proposed/MillerSheffieldIG4.lean`), with the Weyl scaling of paper Facts 2.1 III and 2.2; locator (CHATGPT-frozen-locators.md): MS Proposition 2.9 + DS Proposition 1.1 + GM axiom III.
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
`IsOpen U`). locator (CHATGPT-frozen-locators.md): no exact source; standard via weighted path lengths, GM (1.8).
Used by: firstPass_11_10 (through S11c/Shifted.lean). Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): arclength
parametrization bounds every competing path's E-length by e^B times its D-length, and this upper bound needs no
measurability of f. Source as the answer gives it: deterministic consequence of Gwynne-Miller, arXiv:1905.00383v3,
p. 5, (1.7), and p. 6, Axiom III, (1.8). -/
def WeylInternalClosedFrozen : Prop :=
  ∀ (D E : ℂ → ℂ → ℝ) (ξ B : ℝ) (f : ℂ → ℝ) (U : Set ℂ), IsEuclideanLengthMetric D →
    (∀ x y, 0 ≤ E x y) → (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) → IsClosed U →
    (∀ z ∈ U, ξ * f z ≤ B) → ∀ x y, internalMetric E U x y ≤ ENNReal.ofReal (Real.exp B) * internalMetric D U x y

/-- RETIRED (FALSE, ChatGPT truth check 2026-11-09, operator 19:25 UTC). The metric and the LQG measure are specified only
almost everywhere (`IsLQGMetricOfField`, `IsLQGMeasureOfField`), so a `Measurable` conclusion does not follow from the
field-level inputs. Replaced by the AEMeasurable form `LQGMetricSupMeasurableFrozen`. Former text kept for the record; NOT used.
(Former FIRST-PASS FROZEN: `∀ γ α₀ ξ, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ Ω P hC hcirc D, IsWholePlaneGFF P hC hcirc →
IsLQGMetricOfField P γ ξ α₀ hC D → ∀ K, (∃ F, (∀ R ∈ F, IsClosedRectangle R) ∧ K = ⋃ R ∈ F, R) →
Measurable (fun ω => ⨆ u ∈ K, ⨆ v ∈ K, internalMetric (D ω) K u v)`.) -/
def LQGMetricSupMeasurableRetiredFalseFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ K : Set ℂ, (∃ F : Finset (Set ℂ), (∀ R ∈ F, IsClosedRectangle R) ∧ K = ⋃ R ∈ F, R) →
    Measurable (fun ω => ⨆ u ∈ K, ⨆ v ∈ K, internalMetric (D ω) K u v)

/-- RETIRED (FALSE, ChatGPT truth check 2026-11-09, operator 19:25 UTC). The LQG measure is specified only almost everywhere,
so `Measurable (fun ω => μ ω S)` is not implied by the field-level inputs. Replaced by `LQGMeasureSquareMeasurableFrozen`
(AEMeasurable form). Former text kept for the record; NOT used.
(Former FIRST-PASS FROZEN: `∀ γ α₀, 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ Ω P hC hcirc μ, IsWholePlaneGFF P hC hcirc →
IsLQGMeasureOfField P γ α₀ hcirc μ → ∀ S, IsClosedDyadicSquare S → Measurable (fun ω => μ ω S)`.) -/
def LQGMeasureSquareMeasurableRetiredFalseFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ S : Set ℂ, IsClosedDyadicSquare S → Measurable (fun ω => μ ω S)

/-- FIRST-PASS FROZEN (operator ruling 19:45 UTC, decisions wave 7, item n1 (1); truth check queued). EXTERNAL GFF/LQG
measurability, in AEMeasurable form, for the Weyl-shifted metric of the field: for the LQG measure `μ` and the LQG metric `D`
of a whole-plane GFF (`IsLQGMeasureOfField`, `IsLQGMetricOfField`) and a continuous compactly supported weight `f ≤ 0`, the
supremum over a closed dyadic square `S` of the internal metric of the Weyl-shifted metric `weylShiftPair γ ξ f (μ, D)` is
almost surely measurable. Not stated for arbitrary pairs.
Source: measurability of the LQG metric at field level after Weyl scaling (paper Fact 2.2 III); locator (CHATGPT-frozen-locators.md):
no exact source; standard via GM §1.2 and compact-path coding, as for `LQGMetricSupMeasurableFrozen` (rated implies).
Used by: firstPass_11_10 (through shifted_event_pos_11_10). -/
def WeylShiftedSupMeasurableFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, f z ≤ 0) →
  ∀ S : Set ℂ, IsClosedDyadicSquare S →
    AEMeasurable (fun ω => ⨆ u ∈ S, ⨆ v ∈ S, internalMetric (weylShiftPair γ ξ f (μ ω, D ω)).2 S u v) P

/-- FIRST-PASS FROZEN (operator ruling 19:45 UTC, decisions wave 7, item n1 (1); truth check queued). EXTERNAL GFF/LQG
measurability, in AEMeasurable form, for the Weyl-shifted measure of the field: for the LQG measure `μ` and the LQG metric `D`
of a whole-plane GFF and a continuous compactly supported weight `f ≤ 0`, the mass `(weylShiftPair γ ξ f (μ, D)).1 S` of a
closed dyadic square `S` is almost surely measurable. Not stated for arbitrary pairs.
Source: measurability of the LQG measure at field level after Weyl scaling (paper Fact 2.1 III); locator (CHATGPT-frozen-locators.md):
no exact source; standard via DS Proposition 1.1 and local Weyl multiplication, as for `LQGMassFunctionalMeasurableFrozen` (rated implies).
Used by: firstPass_11_10 (through shifted_event_pos_11_10). -/
def WeylShiftedMassMeasurableFrozen : Prop :=
  ∀ (γ α₀ ξ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    IsLQGMetricOfField P γ ξ α₀ hC D →
  ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∀ z, f z ≤ 0) →
  ∀ S : Set ℂ, IsClosedDyadicSquare S →
    AEMeasurable (fun ω => (weylShiftPair γ ξ f (μ ω, D ω)).1 S) P

/-- The marked restriction observation `(z, h|_D mod ℝ)` of the field `h = h^ℂ - α₀ log|·|` at a root `z`: the pairings of `h`
with the mean-zero test functions `φ` supported in `D` (`fieldSigmaAlgebraModConst`, Draft/Section6.lean:148; constants drop out). -/
noncomputable def campbellMarkedObs (α₀ : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) :=
  (z, fun φ => fieldPairing α₀ hC φ.1)

/-- The reference observation at a root `z`: the restriction to `D` (mod constants) of `g - γ log|·-z| + b`, with
`b(w) = -α₀ log|w| + γ log max(1,|w|)`. Since `fieldPairing α₀ hC φ = (g, φ) - α₀ ∫ φ log|·|`, the pairing with `φ` is
`fieldPairing α₀ hC φ - γ ∫ (log|w - z| - log max(1,|w|)) φ(w) dw`. -/
noncomputable def campbellReferenceObs (γ α₀ : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    ℂ × ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) :=
  (z, fun φ => fieldPairing α₀ hC φ.1 - γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w)

/-- FIRST-PASS FROZEN. EXTERNAL local rooted-field (Campbell–Palm) absolute continuity for the LQG measure of a whole-plane
GFF: the rooted-field change of measure used in the proof of paper Lemma `lemma:mu_h-bad-and-harnack` (Lemma 11.7, paper
line 2896; proof lines 2936-2949), in its stated form. For disks `U = ball c₁ r₁` with `closedBall c₁ r₁ ⊆ D = ball c₂ r₂`,
`0 ∉ closedBall c₂ r₂`, the Campbell law `Q_U(dh, dz) = P(dh) 1_U(z) μ_h(dz) / μ_h(U)` of the LQG measure `μ_h` (insertion `α₀`)
has marked restriction `(z, h|_D mod ℝ)` absolutely continuous with respect to the Lebesgue mixture over `z ∈ U` of the
restrictions of `g - γ log|·-z| + b`, `b(w) = -α₀ log|w| + γ log max(1,|w|)`, where `g` is the GFF on the same space.
Stated as: every measurable set of marked observations that is null for the reference mixture is null for `Q_U`.
Only this one-sided, local statement is used; it is not a statement about cone events.
Source: Duplantier-Miller-Sheffield, arXiv:1409.7055v4, Lemma A.10 (rooting), with Duplantier-Sheffield, arXiv:0808.1560v2,
Proposition 1.1 (LQG measure), and the paper's rooted-field change of measure (line 2936ff); locator
(CHATGPT-frozen-locators.md): no exact source; standard via DMS Lemma A.10 + local Cameron–Martin/GMC pushforward (rated implies).
Not to be confused with `LocalRootedFieldMeasureDomination` (Frozen/S8c.lean), a different statement for Lemma 8.2.
Used by: firstPass_11_7 (route: event-specific transfer, not yet written). -/
def LocalCampbellMarkedRestrictionFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
  IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), 0 < r₁ → 0 < r₂ → closedBall c₁ r₁ ⊆ ball c₂ r₂ → (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∀ S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)), MeasurableSet S →
    (∫⁻ z in ball c₁ r₁, (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P)) = 0 →
    ∫⁻ ω, (μ ω (ball c₁ r₁))⁻¹ * ∫⁻ z in ball c₁ r₁,
        S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) ∂P = 0

/-- FIRST-PASS FROZEN (operator ruling 2026-11-09 20:22 UTC, decision (c); truth-checked style: translation invariance of the
whole-plane GFF modulo additive constants). EXTERNAL: for the whole-plane GFF `h^ℂ` (`IsWholePlaneGFF`), translating the field
by `z` and subtracting a constant does not change its law modulo constants, `g(· + z) - g_1(z) =d g` (Duplantier-Miller-Sheffield,
arXiv:1409.7055v4, Section 4.1, and Holden-Sun, arXiv:1610.05272, proof of Lemma 4.2, p. 16; the covariance
`-log|x - y| + log max(1,|x|) + log max(1,|y|)` is the one of the normalized whole-plane GFF). Truth check 20:44 UTC: TRUE
(citation corrected per operator; not DMS Lemma A.10). Stated as equality of the laws
of the pairings with the mean-zero test functions `φ` (smooth, compact support, `∫ φ = 0`): the constants drop out, so
`(hC ω (φ(· - z)))_φ` and `(hC ω φ)_φ` have the same law. Only the mean-zero pairings are asserted.
Not used by firstPass_11_7 or its chain: the normalized translation `hW'` is proved from `IsWholePlaneGFF` in
`S11c/TranslateField11_7.lean` (`isWholePlaneGFF_translate`), so this input is kept only as a checked statement. Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): translation
preserves the joint Gaussian law of the mean-zero pairings, and the normalization constants disappear. Source as the
answer gives it: Holden-Sun, arXiv:1610.05272v3, p. 16, proof of Lemma 4.2, immediately after (11). -/
def WholePlaneGFFTranslationModConstFrozen : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
  ∀ z : ℂ,
    P.map (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction Set.univ φ ∧ ∫ x, φ x = 0}) => hC ω (fun x => φ.1 (x - z))) =
      P.map (fun ω (φ : {φ : ℂ → ℝ // IsTestFunction Set.univ φ ∧ ∫ x, φ x = 0}) => hC ω φ.1)

/-- FIRST-PASS FROZEN (PENDING OPERATOR APPROVAL AND TRUTH CHECK; not yet approved). EXTERNAL local approximation of the
circle averages of a whole-plane GFF by pairings with mean-zero test functions: for a disk `D` (any open set), a radius `r > 0`,
a fixed normalized bump `ρ` supported in `D` (`∫ ρ = 1`) and a point `z` with `closedBall z r ⊆ D`, there are mean-zero test
functions `φ n` supported in `D` such that the pairings `fieldPairing α₀ (hC) (φ n)` converge in probability to the centred
circle average `h_r(z) - (h, ρ)` of the field `h = h^ℂ - α₀ log|·|`. Standard GFF fact: the smoothed circle measures
`σ_{z,r,η}` (supported in `closedBall z (r + η) ⊆ D` for small `η`) give `(h, σ_{z,r,η}) → h_r(z)` in `L²` by the covariance
`wholePlaneGFFCov` (Duplantier-Sheffield, arXiv:0808.1560v2, Section 3 and Prop. 3.1 for the continuous circle averages);
`φ n = σ_{z,r,η_n} - ρ` (mean zero); the `α₀ log|·|` part of `fieldPairing` and `fieldCircleAverage` converges deterministically.
Stated for the field `h` as in `fieldPairing` and with the base point `ρ` (pairing with a fixed bump), so no circle outside `D`
is used. Only the mean-zero pairings are asserted (constants drop out). Used by: `exists_joint_local_circleAverage_version`
route of firstPass_11_7 (FirstPass/S11c/LocalVersion11_7.lean), i.e. the local decoder K_D of CHATGPT-11-7-B2.md sec 3.1.1. Truth check TRUE (ChatGPT, batch file 02:49 UTC, `notes/fp-gaps/CHATGPT-hb-frozen-batch.md`, table row): smooth
circle mollifications minus ρ converge by the covariance calculation, and the deterministic logarithmic term also
converges. Source as the answer gives it: covariance consequence of Duplantier-Sheffield, arXiv:0808.1560v2, §3.1,
pp. 16-17, (8)-(11) and Proposition 3.1, using the whole-plane covariance in HB v3, p. 8, (2.1). -/
def LocalCircleAverageMeanZeroApproxFrozen : Prop :=
  ∀ (α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
  ∀ (D : Set ℂ), IsOpen D → ∀ (r : ℝ), 0 < r → ∀ ρ : ℂ → ℝ, IsTestFunction D ρ → ∫ x, ρ x = 1 →
  ∀ z : ℂ, closedBall z r ⊆ D →
  ∃ φ : ℕ → ℂ → ℝ, (∀ n, IsTestFunction D (φ n) ∧ ∫ x, φ n x = 0) ∧
    TendstoInMeasure P (fun n ω => fieldPairing α₀ (hC ω) (φ n)) atTop
      (fun ω => fieldCircleAverage α₀ (hcirc ω) r z - fieldPairing α₀ (hC ω) ρ)

/-- The local mean-zero observation of the field `h = h^ℂ - α₀ log|·|` on a set `D`: the pairings of `h` with the
mean-zero test functions supported in `D` (the observation part of `campbellMarkedObs`, without the root). -/
noncomputable def localMeanZeroObs (α₀ : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α₀ hC φ.1

/-- The circle averages of the rooted field `h - γ log|· - z|` (the field rooted at `z`, as in the Campbell law of
`LocalCampbellMarkedRestrictionFrozen`): `h_r(x) - γ · (average of log|· - z| over ∂B_r(x))`. -/
noncomputable def rootedCircleAverage (α₀ γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) (r : ℝ) (x : ℂ) : ℝ :=
  fieldCircleAverage α₀ hcirc r x - γ * Real.circleAverage (fun w => Real.log ‖w - z‖) x r

/-- The mean-zero observation of the rooted field `h - γ log|· - z|` on `D`: the pairings of `h` minus
`γ ∫ log|w - z| φ(w) dw` with the mean-zero test functions supported in `D`. -/
noncomputable def rootedMeanZeroObs (α₀ γ : ℝ) (D : Set ℂ) (z : ℂ) (hC : (ℂ → ℝ) → ℝ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α₀ hC φ.1 - γ * ∫ w, Real.log ‖w - z‖ * φ.1 w

/-- FIRST-PASS FROZEN (operator decision 2026-11-09 21:12 UTC, items 2 and 3). EXTERNAL: one s-finite (measurable)
local decoder kernel `K` from the mean-zero observations on a disk `D = ball c₂ r₂` (`0 ∉ closedBall c₂ r₂`) to
measures on `ℂ`, which
recovers the γ-LQG measure of a whole-plane GFF on `D` up to a constant factor, almost surely, and which does the same
for the rooted field `h - γ log|· - z|` (`z` any point). The first clause is the field `h` itself (`IsLQGMeasureOfField`,
insertion `α₀`); the second clause is the Campbell-rooted field of paper Lemma 11.7 (proof, lines 2936-2949), whose
LQG measure is `IsLQGMeasure` for the profile `rootedCircleAverage`. The constant in B2 eq. (3.2) is
`e^{-γ⟨h,ρ_D⟩}`; only the existence of some constant `c ∈ (0,∞)` is asserted (the cone event is scale-invariant).
Mechanism: the circle averages of `h` on the circles inside `D`, minus the scalar `⟨h, ρ_D⟩` (`ρ_D` the normalized
Lebesgue measure on `D`; this scalar accommodates the missing additive constant), are a.s. limits of mean-zero pairings
(`LocalCircleAverageMeanZeroApproxFrozen`), and the LQG measure is a measurable function of the continuous circle-average
profile on `D` (Duplantier–Sheffield, arXiv:0808.1560v2, Proposition 1.1). Duplantier–Miller–Sheffield, arXiv:1409.7055v4,
Lemma A.10 is a rooting identity, not a decoder theorem: its normalized rooting term `γ log max{|w|,1}` vanishes on the unit
disk but is generally nonconstant on an arbitrary `D`. So the second clause is stated for the pure logarithmic rooted field
`h - γ log|· - z|` actually defined here; identifying it with the Campbell-rooted normalized field needs a domain
qualification or explicit treatment of that term (truth check 21:28 UTC: TRUE as written; notes/fp-gaps/CHATGPT-decoder-truth.md).
Not covered by n4's
`LQGMeasureOfProfileMeasurableFrozen` (`FirstPass/Frozen/S8d.lean:28`): that decoder takes a GLOBAL profile on
`CircleParameter`, and the local observation does not determine the profile outside `D`.
Used by: firstPass_11_7 (route: B2 sec 3-4 decoder, sec 5.1 rooted null section; FirstPass/S11c.lean, to come). -/
def LocalLQGDecoderFrozen : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ → ∀ (c₂ : ℂ) (r₂ : ℝ), 0 < r₂ → (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∃ K : ProbabilityTheory.Kernel ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) ℂ,
    ProbabilityTheory.IsSFiniteKernel K ∧
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = c • (μ ω).restrict (ball c₂ r₂)) ∧
    (∀ (z : ℂ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μz : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ (fun ω => rootedCircleAverage α₀ γ z (hcirc ω)) μz →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        K (rootedMeanZeroObs α₀ γ (ball c₂ r₂) z (hC ω)) = c • (μz ω).restrict (ball c₂ r₂))

/-- FIRST-PASS FROZEN (TRUTH-CHECKED TRUE, ChatGPT 2026-11-09, notes/fp-gaps/CHATGPT-11-7-G1-G2-Q1.md, item G1; operator
22:33 UTC: freeze). EXTERNAL,
common local decoder: for `γ ∈ (0,2)` and a disc `D = ball c₂ r₂` with `0 ∉ closedBall c₂ r₂`, ONE s-finite kernel `K`
from the mean-zero observations on `D` to measures on `ℂ` (clause 1: the γ-LQG measure of the field at every insertion
`α₀ < Q`, up to a constant, a.s.; clause 2: the rooted LQG measure at every root `z` and every insertion `α₀ < Q`,
including `α₀ = 0`, which the origin route of `FixedRoot11_7.lean` uses). This is the common-`K` form of
`LocalLQGDecoderFrozen`, where `K` may depend on `α₀`. Source: Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1,
the fixed smooth compactly supported probability bump `ρ_D` in the decoder (not normalized Lebesgue measure on `D`),
and the rooted clause assumes `IsLQGMeasure` (a locally finite rooted measure is not asserted for every combined insertion).
Source: Duplantier-Sheffield, arXiv:0808.1560v2, Proposition 1.1, Proposition 3.1 and section 3.1 (pairing and circle
covariance construction): a consequence of these constructions, not stated verbatim there (the universal local decoder
uses a countable Borel limit construction). Used by: firstPass_11_7 (`FirstPass/S11c.lean`). -/
def LocalLQGDecoderCommonFrozen : Prop :=
  ∀ (γ : ℝ), 0 < γ → γ < 2 → ∀ (c₂ : ℂ) (r₂ : ℝ), 0 < r₂ → (0 : ℂ) ∉ closedBall c₂ r₂ →
  ∃ K : ProbabilityTheory.Kernel ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) ℂ,
    ProbabilityTheory.IsSFiniteKernel K ∧
    (∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        K (localMeanZeroObs α₀ (ball c₂ r₂) (hC ω)) = c • (μ ω).restrict (ball c₂ r₂)) ∧
    (∀ α₀ : ℝ, α₀ < lqgQ γ → ∀ (z : ℂ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μz : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasure P γ (fun ω => rootedCircleAverage α₀ γ z (hcirc ω)) μz →
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, 0 < c ∧ c < ⊤ ∧
        K (rootedMeanZeroObs α₀ γ (ball c₂ r₂) z (hC ω)) = c • (μz ω).restrict (ball c₂ r₂))

/-- FIRST-PASS FROZEN (TRUTH-CHECKED TRUE, ChatGPT 2026-11-09, notes/fp-gaps/CHATGPT-11-7-G1-G2-Q1.md, item G2, option A;
operator 22:33 UTC: freeze exactly as stated). Non-smooth Cameron-Martin for the
shift `χ_b = b χ` of B2 sec 5.2). EXTERNAL, Cameron-Martin for locally Lipschitz compactly supported shifts of the
whole-plane GFF, read on the mean-zero pairings with the test functions supported in a set `D`: for `g` locally
Lipschitz with compact support (it lies in the Cameron-Martin space, which contains the compactly supported functions of
finite Dirichlet energy), a measurable set of observations that is null for the unshifted pairings `hC` is null for the
shifted pairings `hC + ∫ φ g`. Mean-zero pairings do not see the additive constant of the normalisation, so no unit-circle
average constraint is needed (contrast `CameronMartinGFFMutualAbsCont`, which needs smooth `g` with zero unit-circle
average). Only this one-sided direction is used. Source: Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2,
Proposition 2.9 (Dirichlet space, section 2.2.1), which covers this shift. Used by: firstPass_11_7
(`FirstPass/S11c/ShiftCM11_7.lean`). -/
def CameronMartinLocallyLipschitzShiftAbsCont : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (D : Set ℂ) (g : ℂ → ℝ), IsWholePlaneGFF P hC hcirc → LocallyLipschitz g →
    HasCompactSupport g → ∀ S : Set ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ), MeasurableSet S →
    P {ω | (fun φ => hC ω φ.1) ∈ S} = 0 → P {ω | (fun φ => hC ω φ.1 + ∫ x, φ.1 x * g x) ∈ S} = 0

end HarmonicBalls
