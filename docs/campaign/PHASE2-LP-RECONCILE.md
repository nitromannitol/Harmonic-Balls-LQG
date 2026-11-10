# Phase 2 reconcile: HB objects against LP and elliptic_regularity objects

Task fp-phase2-m1-reconcile (z4, 2026-11-10). Facts only: signatures, fields, carriers, counts, bridge shapes; no equivalence is claimed or judged. Sources: HB `HarmonicBalls/` (HEAD 45eeb817 when read); LP `LatticeProb/` (Lattice-Probability-v435 at 3912597, the HB pin); ER = elliptic_regularity package; Mathlib under `.lake/packages/mathlib/Mathlib/`. Lines are the `def`/`structure` keyword lines. Pairs: SPEC section 2, items diff1-4 and part1-7.
Method: counts from `scratch-z4/count_blocks.py`; files = whole-word matches (equal to `grep -rlw`), blocks = declaration blocks (keyword line to next blank line) containing the name. Bridge types are Lean text, not elaborated (no `.lean` file). Carrier maps absent from the code (no map `(ℂ → ℝ) → ℝ` to `LQGMetric.DistC`, none `ℂ → ℂ → ℝ` to `ContMetric`, no `Vec 2 ≃ ℂ` with a coefficient field for `Δ`; `HarmonicBalls/Defs/` mentions no `DistC`): bridges take them as existentials.

## P1 IsWholePlaneGFF (diff1)
```lean
-- HB Defs/GFF.lean:93
structure IsWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop
  -- fields: measurable_pairing, measurable_circle, isGaussianProcess (GFFObservable.Admissible), integral_eq_zero, covariance_eq (wholePlaneGFFCov), ae_continuousOn_circle
-- LP Bonanno/LQGMetric/Statement/GFF.lean:41 (DistC := DistOn ⊤, Statement/Field.lean:48; TestC0 := {φ : TestC // ∫ φ = 0}, GFF.lean:33)
structure IsWholePlaneGFF (h : Ω → DistC) (P : Measure Ω) : Prop
  -- fields: measurable, gaussian (TestC0), centered, covariance_eq (logCov)
HB → LP: ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), HarmonicBalls.IsWholePlaneGFF P hC hcirc → ∃ h : Ω → LQGMetric.DistC, LQGMetric.IsWholePlaneGFF h P ∧ ∀ (ω : Ω) (φ : LQGMetric.TestC0), h ω φ.1 = hC ω ⇑φ.1
LP → HB: ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → LQGMetric.DistC), LQGMetric.IsWholePlaneGFF h P → ∃ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), HarmonicBalls.IsWholePlaneGFF P hC hcirc ∧ ∀ (ω : Ω) (φ : LQGMetric.TestC0), hC ω ⇑φ.1 = h ω φ.1
```
Syntax: HB takes two data arguments (pairings on all `ℂ → ℝ`, circle averages); LP takes one, `h : Ω → DistC`. HB's Gaussian and centering clauses range over pairings and circle averages together; LP's over mean-zero test functions. HB's circle-average fields have no LP field.
Counts: HB 1372 files / 2619 blocks; LP 62 / 184.

## P2 fieldCircleAverage / IsGFFCircleAverage (diff2)
```lean
-- HB Defs/GFF.lean:118 (def; no Ω, no measure)
noncomputable def fieldCircleAverage (α₀ : ℝ) (hcirc : ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) : ℝ := hcirc r z - α₀ * Real.circleAverage (fun x => Real.log ‖x‖) z r
-- LP Bonanno/LQGDimension/Statement/Defs.lean:106 (gffCircleCov :98)
structure IsGFFCircleAverage {Ω : Type*} [MeasurableSpace Ω] (h : ℝ → ℂ → Ω → ℝ) (P : Measure Ω) : Prop
  -- fields: isProbabilityMeasure, isGaussianProcess, integral_eq_zero, covariance_eq (gffCircleCov), continuous
HB → LP: ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), HarmonicBalls.IsWholePlaneGFF P hC hcirc → LQGDimension.IsGFFCircleAverage (fun ε z ω => hcirc ω ε z) P
LP → HB: ∀ {Ω : Type*} [MeasurableSpace Ω] (h : ℝ → ℂ → Ω → ℝ) (P : Measure Ω), LQGDimension.IsGFFCircleAverage h P → ∃ hC : Ω → (ℂ → ℝ) → ℝ, HarmonicBalls.IsWholePlaneGFF P hC (fun ω ε z => h ε z ω)
```
Syntax: HB is a value from data `hcirc` and a parameter `α₀` (the `α₀` term has no LP counterpart); LP is a predicate on a family over `Ω` with a measure, indexed by `ε > 0`.
Counts: HB 221 / 355; LP 18 / 55.

## P3 weylScaling / weylScale (part5)
```lean
-- HB Defs/LQGMetric.lean:107 (IsLengthParametrized :99)
noncomputable def weylScaling (D : ℂ → ℂ → ℝ) (ξ : ℝ) (f : ℂ → ℝ) (u v : ℂ) : ℝ≥0∞ := ⨅ (T : ℝ) (p : ℝ → ℂ) (_ : IsLengthParametrized D p T) (_ : p 0 = u) (_ : p T = v), ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t)))
-- LP Bonanno/LQGMetric/Statement/Metric.lean:96 (ContMetric := {d : C(ℂ × ℂ, ℝ) // IsContinuousMetric d}, :50; ContMetric.Space := ℂ, :75; instance dist x y := D.1 (x, y), :78)
def weylScale (ξ : ℝ) (f : C(ℂ, ℝ)) (D : ContMetric) (z w : ℂ) : ℝ≥0∞ := ⨅ (L : ℝ) (P : ℝ → ℂ) (_ : 0 ≤ L) (_ : ContinuousOn (D.pt ∘ P) (Icc 0 L)) (_ : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) (_ : P 0 = z) (_ : P L = w), ∫⁻ t in Icc 0 L, ENNReal.ofReal (Real.exp (ξ * f (P t)))
-- Bridge (one equation; HB → LP needs a ContMetric lift, LP → HB reads it backwards)
∀ (Dc : LQGMetric.ContMetric) (ξ : ℝ) (fc : C(ℂ, ℝ)) (z w : ℂ), HarmonicBalls.weylScaling (fun a b => Dc.1 (a, b)) ξ ⇑fc z w = LQGMetric.weylScale ξ fc Dc z w
```
Syntax: HB `D` is any `ℂ → ℂ → ℝ`, LP `D` is a continuous metric; HB `f : ℂ → ℝ`, LP `f : C(ℂ, ℝ)`; argument order `(D ξ f u v)` versus `(ξ f D z w)`; path condition via `curveLength` (HB) versus `HasUnitSpeedOn` in `D.Space` (LP).
Counts: HB 266 / 443; LP 6 / 16.

## P4 lqgApprox / GMSLemma27.lqgApprox (part1)
```lean
-- HB Defs/LQG.lean:46
noncomputable def lqgApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε z))
-- LP Bonanno/MatedCRTHarmonic/GMSLemma27/GMCInterfaces.lean:43 (dyadicRadius k := (2 : ℝ) ^ (-(k : ℤ)), :39)
def lqgApprox {Ω : Type*} (γ : ℝ) (H : ℝ → ℂ → Ω → ℝ) (k : ℕ) (ω : Ω) : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (dyadicRadius k ^ (γ ^ 2 / 2) * Real.exp (γ * H (dyadicRadius k) z ω))
-- Bridge (one equation, both directions)
∀ (γ : ℝ) (hε : ℝ → ℂ → ℝ) (k : ℕ) {Ω : Type*} (ω : Ω), HarmonicBalls.lqgApprox γ hε (MatedCRTHarmonic.GMSLemma27.dyadicRadius k) = MatedCRTHarmonic.GMSLemma27.lqgApprox γ (fun ε z (_ : Ω) => hε ε z) k ω
```
Syntax: same body with `ε` replaced by `dyadicRadius k`; HB has a real scale and a deterministic family, LP a dyadic index `k : ℕ` and an extra `ω`. No hypothesis in either.
Counts: HB 55 / 85; LP 3 / 8.

## P5 IsEuclideanLengthMetric / ContMetric.IsLength, IsStrongLQGMetric.length (part2)
```lean
-- HB Defs/LQGMetric.lean:81
structure IsEuclideanLengthMetric (D : ℂ → ℂ → ℝ) : Prop
  -- fields: self_eq_zero, eq_of_eq_zero, symm, triangle, isOpen_iff (IsOpen U ↔ …), ofReal_eq_internalMetric
-- LP Bonanno/LQGMetric/Statement/Metric.lean:92 (IsMetricFn :38; IsContinuousMetric :46 extends IsMetricFn, field euclidean_of_small); length field of IsStrongLQGMetric (Statement/LQGMetric.lean:38)
def ContMetric.IsLength (D : ContMetric) : Prop := MetricGeometry.IsLengthSpace D.Space
HB → LP: ∀ (D : ℂ → ℂ → ℝ), HarmonicBalls.IsEuclideanLengthMetric D → ∃ Dc : LQGMetric.ContMetric, (∀ a b, Dc.1 (a, b) = D a b) ∧ Dc.IsLength
LP → HB: ∀ Dc : LQGMetric.ContMetric, Dc.IsLength → HarmonicBalls.IsEuclideanLengthMetric (fun a b => Dc.1 (a, b))
```
Syntax: HB has no continuity field; LP's continuity is in the carrier `C(ℂ × ℂ, ℝ)`. HB's Euclidean clause is an equivalence (`isOpen_iff`), LP's one inclusion (`euclidean_of_small`). LP's length is a property of `D.Space`, quantified a.s. in the strong structure; HB's is `ofReal_eq_internalMetric`.
Counts: HB 420 / 941; LP 1 / 1.

## P6 internalMetric / ContMetric.internal (part6)
```lean
-- HB Defs/LQGMetric.lean:65 (pathLength :60 := curveLength D P.extend 0 1; curveLength :55)
noncomputable def internalMetric (D : ℂ → ℂ → ℝ) (U : Set ℂ) (z w : ℂ) : ℝ≥0∞ := ⨅ (P : Path z w) (_ : ∀ t, P t ∈ U), pathLength D P
-- LP Statement/Metric.lean:89 (internalEDist: Bonanno/LQGMetric/Metric/LengthSpace.lean:120, namespace LQGMetric.MetricGeometry; pathLength :39; curveLength Metric/CurveLength.lean:42)
def ContMetric.internal (D : ContMetric) (U : Set ℂ) (z w : ℂ) : ℝ≥0∞ := MetricGeometry.internalEDist (D.pt '' U) (D.pt z) (D.pt w)
-- Bridge (one equation, both directions)
∀ (Dc : LQGMetric.ContMetric) (U : Set ℂ) (z w : ℂ), HarmonicBalls.internalMetric (fun a b => Dc.1 (a, b)) U z w = Dc.internal U z w
```
Syntax: both are infima over paths in `U` of a length. HB paths live in `ℂ`, Euclidean; LP paths in `D.Space` with metric `D.1 (x, y)`. HB's `U` is passed directly; LP's as `D.pt '' U`. A second copy of `internalEDist` is at LatticeProb/Topology/Length/LengthSpace.lean:124.
Counts: HB 349 / 686; LP `ContMetric.internal` 5 / 7; LP `internalEDist` 10 / 47.

## P7 SatisfiesLQGMetricAxioms, IsLQGMetric / IsStrongLQGMetric, IsWeakLQGMetric (diff3, part3); LQGMetricFieldAxioms (part4)
```lean
-- HB Defs/LQGMetric.lean:179 IsLQGMetric (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ); fields measurable_apply, satisfiesLQGMetricAxioms (for IsWholePlaneGFF P hC hcirc and continuous random f)
-- HB Defs/LQGMetric.lean:146 SatisfiesLQGMetricAxioms (P γ ξ 𝔇 h); fields ae_isEuclideanLengthMetric, locality, ae_weylScaling, coordChange
-- LP Bonanno/LQGMetric/Statement/LQGMetric.lean:38 structure IsStrongLQGMetric (γ : ℝ) (D : DistC → ContMetric); fields measurable, length, locality, weyl, coord
-- LP same file :82 structure IsWeakLQGMetric (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ); fields measurable, length, locality, weyl, translation, tightness (TightAcrossScales :65)
-- HB Proposed/LQG.lean:225 LQGMetricFieldAxioms (P γ ξ α₀ hC hcirc): premises IsWholePlaneGFF, 0 < γ < 2, α₀ < lqgQ γ; clauses I–IV for weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖)
HB → LP: ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), HarmonicBalls.IsLQGMetric γ ξ 𝔇 → ξ = LQGMetric.xiGamma γ → ∃ D : LQGMetric.DistC → LQGMetric.ContMetric, LQGMetric.IsStrongLQGMetric γ D
LP → HB: ∀ (γ : ℝ) (D : LQGMetric.DistC → LQGMetric.ContMetric), LQGMetric.IsStrongLQGMetric γ D → ∃ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, HarmonicBalls.IsLQGMetric γ (LQGMetric.xiGamma γ) 𝔇
```
Syntax: HB's `ξ` is a parameter; LP fixes `xiGamma γ` (Statement/Dimension.lean:62). HB's metric is on functionals `(ℂ → ℝ) → ℝ`, LP's on `DistC`. Only LP's weak structure has translation and tightness. LP has no `α₀`-shifted field: `addFun (h : DistC) (f : C(ℂ, ℝ))` (Statement/Field.lean:57) takes a continuous `f`; HB's shift `-α₀ log‖·‖` is a bare `ℂ → ℝ`.
Counts: HB `IsLQGMetric` 217 / 326; `SatisfiesLQGMetricAxioms` 12 / 8; `LQGMetricFieldAxioms` 122 / 142; LP `IsStrongLQGMetric` 3 / 6; `IsWeakLQGMetric` 11 / 44.

## P8 IsHarmonicMinorant / IsHarmonicOn (diff4)
```lean
-- HB Defs/Green.lean:54
def IsHarmonicMinorant (O : Set ℂ) (u : ℂ → EReal) (h : ℂ → ℝ) : Prop := InnerProductSpace.HarmonicOnNhd h O ∧ ∀ y ∈ O, (h y : EReal) ≤ u y
-- LP Analysis/HarmonicBridge.lean:31 (namespace LatticeProb; E an inner product space over ℝ)
def IsHarmonicOn (h : E → ℝ) (U : Set E) : Prop := ContDiffOn ℝ 2 h U ∧ ∀ x ∈ U, Δ h x = 0
-- Mathlib Analysis/InnerProductSpace/Harmonic/Basic.lean:48, :41: HarmonicOnNhd := ∀ x ∈ s, HarmonicAt f x; HarmonicAt := ContDiffAt ℝ 2 f x ∧ (Δ f =ᶠ[𝓝 x] 0)
HB → LP: ∀ (O : Set ℂ) (u : ℂ → EReal) (h : ℂ → ℝ), HarmonicBalls.IsHarmonicMinorant O u h → LatticeProb.IsHarmonicOn h O
LP → HB: ∀ (O : Set ℂ) (u : ℂ → EReal) (h : ℂ → ℝ), LatticeProb.IsHarmonicOn h O → (∀ y ∈ O, (h y : EReal) ≤ u y) → HarmonicBalls.IsHarmonicMinorant O u h
```
Syntax: HB adds a minorant clause for `u : ℂ → EReal`; LP has none. HB's regularity is pointwise (`ContDiffAt`, eventual Δ = 0); LP's is on `U`.
Counts: HB 30 / 61; LP 11 / 28.

## P9 greenFunction / PDE.IsGreenFunction (part7)
```lean
-- HB Defs/Green.lean:70
noncomputable def greenFunction (O : Set ℂ) (x y : ℂ) : ℝ := if x ∈ O ∧ y ∈ O ∧ x ≠ y then newtonKernel x y - (greatestHarmonicMinorant O (newtonKernelEReal x) y).toReal else 0
-- ER EllipticRegularity/Green/GreenFunctionDef.lean:15 (namespace PDE); Vec d := Fin d → ℝ (PDEFoundation/Ambient/Basic.lean:19); CoeffField d := Vec d → Mat d (PDEFoundation/Ambient/CoefficientField.lean:24)
def IsGreenFunction {d : ℕ} (a : CoeffField d) (R : ℝ) (G : Vec d → ℝ) : Prop := Measurable G ∧ (∀ ε, 0 < ε → ε < R → MemL2On (euclideanBall 0 R \ euclideanBall 0 ε) G) ∧ …
-- HB → ER
∀ (R : ℝ), 0 < R → ∃ (e : PDE.Vec 2 ≃ ℂ) (a : PDE.CoeffField 2), e 0 = 0 ∧ PDE.IsGreenFunction a R (fun v => HarmonicBalls.greenFunction (Metric.ball (0 : ℂ) R) 0 (e v))
-- ER → HB
∀ (a : PDE.CoeffField 2) (R : ℝ) (G : PDE.Vec 2 → ℝ), PDE.IsGreenFunction a R G → ∃ e : PDE.Vec 2 ≃ ℂ, e 0 = 0 ∧ ∀ v, G v = HarmonicBalls.greenFunction (Metric.ball (0 : ℂ) R) 0 (e v)
```
Syntax: HB is a two-point function on any open `O ⊆ ℂ`, from the Newtonian kernel and a harmonic minorant, with no coefficient field. ER is a predicate on one function on `Vec d` for a ball `B_R` at 0, with coefficient field `a` and its adjoint (ER docstring: Green function of `-div(a∇·)` with pole at the origin).
Counts: HB 285 / 745; ER 21 / 27.
