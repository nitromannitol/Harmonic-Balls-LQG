import HarmonicBalls.FirstPass.S11ag.Metric
import HarmonicBalls.FirstPass.S11m.LocalRule
import HarmonicBalls.Steps.Sec11.PinchNormalizedLocalEvent

/-!
# Decoded local rule: countable form and identification with the true rule

Equation (2) (the local certificate
`E₁ ∩ E₂(M) ∩ E₃`) and section 5 (one measurable rule; nonfinite outputs rejected, l.383-409).

Let `X` be a measurable space of observations. The decoded data are values `Φ O x y ℓ : ℝ≥0∞`, indexed by open domains
`O` and points `x, y` (the decoded internal metric on `O`, Armitage-Gardiner internal distance), and decoded masses
`mS ℓ`, `mU ℓ` standing for `S = annulusGreenPotentialSup μ 0 3 6` and `μ U`. `decodedPinchRule` is the set of
observations at which the five strict inequalities of equation (2) hold in their countable forms (`S11ae.localFirstCount`,
`S11ae.localThirdCount`, `S11ag.secondMetric_iff_count`) on the countable dense sets of `PinchCountSets`, with every
right-hand side and every mass required to be finite.

* `measurableSet_decodedPinchRule`: the decoded rule is measurable for measurable decoders (no continuity in `ℓ`).
* `decodedPinchRule_iff`: if the decoded metric equals `b` times the internal metric of a Euclidean length metric `D` on
  the countable point sets (`DecodesOnSets`) and the decoded masses equal `c` times the `μ`-masses (`0 < b`, `0 < c`), then
  `ℓ` lies in the decoded rule iff the true local certificate `pinchLocalRule μ D` holds and the two mass quantities are
  finite. The only inputs are the geometry `IsBufferedPinchGeometry` and the inclusion `hΩ`.
-/

namespace HarmonicBalls.S11am

open MeasureTheory Set Metric Filter
open scoped ENNReal

variable {X : Type*}
variable {U V W T Q' Q : Set ℂ} {δ : ℝ}

/-- `S` is a countable dense subset of `A`: `S ⊆ A`, `A ⊆ closure S`, `S` countable (the index sets of the countable
forms of `S11ae/Count.lean` and `S11ag/Metric.lean`). -/
abbrev IsCountDenseIn (S A : Set ℂ) : Prop :=
  S ⊆ A ∧ A ⊆ closure S ∧ S.Countable

/-- The countable index sets of the local certificate for the pinch geometry `(V, W, T, Q', Q, δ)`.
`E₁`: `sp` dense in `∂B₅` (the supremum `A`), `qp` dense in `closure Q'` and `fp` dense in `∂Q` (the distance `L`),
`cp` dense in `closure (T \ B_{3δ}(W))` (the diameter `d₀`), `ep` dense in `∂B_δ` (the distance `a₀`).
`E₂`: `s2` dense in `∂B_δ`, `s3` dense in `∂B_{2δ}` (the distance `a₁`), `cv` dense in `closure V` (the diameter `d₁`).
`E₃`: `t2` dense in `∂B_{2δ}`, `t3` dense in `∂B_{3δ}` (the distance `a₂`), `ct` dense in `closure (B_{3δ}(W) \ V)`
(the diameter `d₂`). -/
structure PinchCountSets (V W T Q' Q : Set ℂ) (δ : ℝ) where
  sp : Set ℂ
  sp_dense : IsCountDenseIn sp (sphere (0 : ℂ) 5)
  qp : Set ℂ
  qp_dense : IsCountDenseIn qp (closure Q')
  fp : Set ℂ
  fp_dense : IsCountDenseIn fp (frontier Q)
  cp : Set ℂ
  cp_dense : IsCountDenseIn cp (closure (T \ thickening (3 * δ) W))
  ep : Set ℂ
  ep_dense : IsCountDenseIn ep (sphere (0 : ℂ) δ)
  s2 : Set ℂ
  s2_dense : IsCountDenseIn s2 (sphere (0 : ℂ) δ)
  s3 : Set ℂ
  s3_dense : IsCountDenseIn s3 (sphere (0 : ℂ) (2 * δ))
  cv : Set ℂ
  cv_dense : IsCountDenseIn cv (closure V)
  t2 : Set ℂ
  t2_dense : IsCountDenseIn t2 (sphere (0 : ℂ) (2 * δ))
  t3 : Set ℂ
  t3_dense : IsCountDenseIn t3 (sphere (0 : ℂ) (3 * δ))
  ct : Set ℂ
  ct_dense : IsCountDenseIn ct (closure (thickening (3 * δ) W \ V))

/-! ### The decoded rule -/

/-- Decoded first local event `E₁`: the countable form `S11ae.localFirstCount` on the decoded values, with the two
infima (the right sides of its inequalities) finite. -/
def decodedFirstCount (I : PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (ℓ : X) : Prop :=
  S11ae.localFirstCount (fun O x y => Φ O x y ℓ) (pinchOmegaGeom W Q δ)
      (thickening δ (closure (T \ thickening (3 * δ) W))) I.sp I.qp I.fp I.cp I.ep ∧
    (⨅ p ∈ I.qp, ⨅ q ∈ I.fp, Φ univ p q ℓ) ≠ ⊤ ∧ (⨅ p ∈ I.ep, Φ univ 0 p ℓ) ≠ ⊤

/-- Decoded second local event `E₂(M)`: the countable metric clause `S11ae.localThirdCount` on the domain `B_δ(closure V)`
with finite right side, and the mass clause `M · S < μ(U)` on the decoded masses, both finite. -/
def decodedSecondCount (I : PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞)
    (mS mU : X → ℝ≥0∞) (M : ℝ) (ℓ : X) : Prop :=
  S11ae.localThirdCount (fun O x y => Φ O x y ℓ) (thickening δ (closure V)) I.s2 I.s3 I.cv ∧
    (⨅ p ∈ I.s2, ⨅ q ∈ I.s3, Φ univ p q ℓ) ≠ ⊤ ∧
    (mS ℓ ≠ ⊤ ∧ mU ℓ ≠ ⊤ ∧ ENNReal.ofReal M * mS ℓ < mU ℓ)

/-- Decoded third local event `E₃`: the countable form `S11ae.localThirdCount` on `B_δ(closure (B_{3δ}(W) \ V))`, with
finite right side. -/
def decodedThirdCount (I : PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (ℓ : X) : Prop :=
  S11ae.localThirdCount (fun O x y => Φ O x y ℓ) (thickening δ (closure (thickening (3 * δ) W \ V)))
      I.t2 I.t3 I.ct ∧
    (⨅ p ∈ I.t2, ⨅ q ∈ I.t3, Φ univ p q ℓ) ≠ ⊤

/-- The decoded local rule `E = E₁ ∩ E₂(M) ∩ E₃` of equation (2), with nonfinite outputs rejected (route section 5). -/
def decodedPinchRule (I : PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞)
    (mS mU : X → ℝ≥0∞) (M : ℝ) : Set X :=
  {ℓ | decodedFirstCount I Φ ℓ ∧ decodedSecondCount I Φ mS mU M ℓ ∧ decodedThirdCount I Φ ℓ}

/-! ### Measurability (for `distributionMeasurableSpace`-free, generic `X`) -/

/-- `{ℓ | f ℓ ≠ ⊤}` is measurable for a measurable `f`. -/
theorem measurableSet_ne_top_of [MeasurableSpace X] {f : X → ℝ≥0∞} (hf : Measurable f) : MeasurableSet {ℓ | f ℓ ≠ ⊤} :=
  (hf (measurableSet_singleton ⊤)).compl

/-- The decoded first event is a measurable set of observations, for measurable decoders on open domains. -/
theorem measurableSet_decodedFirstCount [MeasurableSpace X] (I : PinchCountSets V W T Q' Q δ) {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞}
    (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ) :
    MeasurableSet {ℓ | decodedFirstCount I Φ ℓ} := by
  have hO : IsOpen (pinchOmegaGeom W Q δ) := HarmonicBalls.S11m.E1Bounds.pinchOmegaGeom_isOpen W Q δ
  have m1 : Measurable fun ℓ => ⨆ y ∈ I.sp, Φ (pinchOmegaGeom W Q δ) 0 y ℓ :=
    measurable_iSup_mem_of_countable I.sp_dense.2.2 fun y => hΦ _ hO 0 y
  have m2 : Measurable fun ℓ => ⨅ p ∈ I.qp, ⨅ q ∈ I.fp, Φ univ p q ℓ :=
    measurable_iInf_mem_of_countable I.qp_dense.2.2 fun p =>
      measurable_iInf_mem_of_countable I.fp_dense.2.2 fun q => hΦ univ isOpen_univ p q
  have m3 : Measurable fun ℓ =>
      ⨆ x ∈ I.cp, ⨆ y ∈ I.cp, Φ (thickening δ (closure (T \ thickening (3 * δ) W))) x y ℓ :=
    measurable_iSup_mem_of_countable I.cp_dense.2.2 fun x =>
      measurable_iSup_mem_of_countable I.cp_dense.2.2 fun y => hΦ _ isOpen_thickening x y
  have m4 : Measurable fun ℓ => ⨅ p ∈ I.ep, Φ univ 0 p ℓ :=
    measurable_iInf_mem_of_countable I.ep_dense.2.2 fun p => hΦ univ isOpen_univ 0 p
  have hloc : MeasurableSet {ℓ | S11ae.localFirstCount (fun O x y => Φ O x y ℓ) (pinchOmegaGeom W Q δ)
      (thickening δ (closure (T \ thickening (3 * δ) W))) I.sp I.qp I.fp I.cp I.ep} := by
    unfold S11ae.localFirstCount
    exact (measurableSet_lt m1 m2).inter (measurableSet_lt m3 m4)
  exact hloc.inter ((measurableSet_ne_top_of m2).inter (measurableSet_ne_top_of m4))

/-- The decoded second event is a measurable set of observations, for measurable decoders and masses. -/
theorem measurableSet_decodedSecondCount [MeasurableSpace X] (I : PinchCountSets V W T Q' Q δ) {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞}
    (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ) {mS mU : X → ℝ≥0∞}
    (hmS : Measurable mS) (hmU : Measurable mU) (M : ℝ) :
    MeasurableSet {ℓ | decodedSecondCount I Φ mS mU M ℓ} := by
  have m1 : Measurable fun ℓ => ⨆ x ∈ I.cv, ⨆ y ∈ I.cv, Φ (thickening δ (closure V)) x y ℓ :=
    measurable_iSup_mem_of_countable I.cv_dense.2.2 fun x =>
      measurable_iSup_mem_of_countable I.cv_dense.2.2 fun y => hΦ _ isOpen_thickening x y
  have m2 : Measurable fun ℓ => ⨅ p ∈ I.s2, ⨅ q ∈ I.s3, Φ univ p q ℓ :=
    measurable_iInf_mem_of_countable I.s2_dense.2.2 fun p =>
      measurable_iInf_mem_of_countable I.s3_dense.2.2 fun q => hΦ univ isOpen_univ p q
  have hloc : MeasurableSet {ℓ | S11ae.localThirdCount (fun O x y => Φ O x y ℓ) (thickening δ (closure V))
      I.s2 I.s3 I.cv} := by
    unfold S11ae.localThirdCount
    exact measurableSet_lt m1 m2
  have hmass : MeasurableSet {ℓ | mS ℓ ≠ ⊤ ∧ mU ℓ ≠ ⊤ ∧ ENNReal.ofReal M * mS ℓ < mU ℓ} :=
    (measurableSet_ne_top_of hmS).inter
      ((measurableSet_ne_top_of hmU).inter (measurableSet_lt (hmS.const_mul _) hmU))
  exact hloc.inter ((measurableSet_ne_top_of m2).inter hmass)

/-- The decoded third event is a measurable set of observations, for measurable decoders on open domains. -/
theorem measurableSet_decodedThirdCount [MeasurableSpace X] (I : PinchCountSets V W T Q' Q δ) {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞}
    (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ) :
    MeasurableSet {ℓ | decodedThirdCount I Φ ℓ} := by
  have m1 : Measurable fun ℓ =>
      ⨆ x ∈ I.ct, ⨆ y ∈ I.ct, Φ (thickening δ (closure (thickening (3 * δ) W \ V))) x y ℓ :=
    measurable_iSup_mem_of_countable I.ct_dense.2.2 fun x =>
      measurable_iSup_mem_of_countable I.ct_dense.2.2 fun y => hΦ _ isOpen_thickening x y
  have m2 : Measurable fun ℓ => ⨅ p ∈ I.t2, ⨅ q ∈ I.t3, Φ univ p q ℓ :=
    measurable_iInf_mem_of_countable I.t2_dense.2.2 fun p =>
      measurable_iInf_mem_of_countable I.t3_dense.2.2 fun q => hΦ univ isOpen_univ p q
  have hloc : MeasurableSet {ℓ | S11ae.localThirdCount (fun O x y => Φ O x y ℓ)
      (thickening δ (closure (thickening (3 * δ) W \ V))) I.t2 I.t3 I.ct} := by
    unfold S11ae.localThirdCount
    exact measurableSet_lt m1 m2
  exact hloc.inter (measurableSet_ne_top_of m2)

/-- **Measurability of the decoded rule.** For measurable decoders on open domains and measurable decoded masses, the
set of observations at which the decoded local certificate holds is measurable. -/
theorem measurableSet_decodedPinchRule [MeasurableSpace X] (I : PinchCountSets V W T Q' Q δ) {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞}
    (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ) {mS mU : X → ℝ≥0∞}
    (hmS : Measurable mS) (hmU : Measurable mU) (M : ℝ) :
    MeasurableSet (decodedPinchRule I Φ mS mU M) := by
  unfold decodedPinchRule
  exact (measurableSet_decodedFirstCount I hΦ).inter
    ((measurableSet_decodedSecondCount I hΦ hmS hmU M).inter (measurableSet_decodedThirdCount I hΦ))

/-! ### Identification with the true local rule -/

/-- The decoded values at `ℓ` are `b` times the internal metric of `D` on the countable point sets of `I` (on the
domains of the three local events). -/
def DecodesOnSets (I : PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (D : ℂ → ℂ → ℝ) (b : ℝ)
    (ℓ : X) : Prop :=
  (∀ y ∈ I.sp, Φ (pinchOmegaGeom W Q δ) 0 y ℓ = ENNReal.ofReal b * internalMetric D (pinchOmegaGeom W Q δ) 0 y) ∧
  (∀ p ∈ I.qp, ∀ q ∈ I.fp, Φ univ p q ℓ = ENNReal.ofReal b * internalMetric D univ p q) ∧
  (∀ x ∈ I.cp, ∀ y ∈ I.cp, Φ (thickening δ (closure (T \ thickening (3 * δ) W))) x y ℓ =
      ENNReal.ofReal b * internalMetric D (thickening δ (closure (T \ thickening (3 * δ) W))) x y) ∧
  (∀ p ∈ I.ep, Φ univ 0 p ℓ = ENNReal.ofReal b * internalMetric D univ 0 p) ∧
  (∀ x ∈ I.cv, ∀ y ∈ I.cv, Φ (thickening δ (closure V)) x y ℓ =
      ENNReal.ofReal b * internalMetric D (thickening δ (closure V)) x y) ∧
  (∀ p ∈ I.s2, ∀ q ∈ I.s3, Φ univ p q ℓ = ENNReal.ofReal b * internalMetric D univ p q) ∧
  (∀ x ∈ I.ct, ∀ y ∈ I.ct, Φ (thickening δ (closure (thickening (3 * δ) W \ V))) x y ℓ =
      ENNReal.ofReal b * internalMetric D (thickening δ (closure (thickening (3 * δ) W \ V))) x y) ∧
  (∀ p ∈ I.t2, ∀ q ∈ I.t3, Φ univ p q ℓ = ENNReal.ofReal b * internalMetric D univ p q)

/-- `ofReal b * S ≠ ⊤` for a positive real `b` and `S : ℝ≥0∞`. -/
theorem ofReal_mul_ne_top_iff {c : ℝ} (hc : 0 < c) (S : ℝ≥0∞) : ENNReal.ofReal c * S ≠ ⊤ ↔ S ≠ ⊤ := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  constructor
  · intro h hS
    exact h (by rw [hS, ENNReal.mul_top hc0])
  · intro h
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h

/-- The mass clause is invariant under the common factor `c > 0` of the decoded masses. -/
theorem mass_scaled_iff {c M : ℝ} (hc : 0 < c) (S U : ℝ≥0∞) :
    (ENNReal.ofReal c * S ≠ ⊤ ∧ ENNReal.ofReal c * U ≠ ⊤ ∧
        ENNReal.ofReal M * (ENNReal.ofReal c * S) < ENNReal.ofReal c * U) ↔
      (S ≠ ⊤ ∧ U ≠ ⊤ ∧ ENNReal.ofReal M * S < U) := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hcT : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ofReal_mul_ne_top_iff hc, ofReal_mul_ne_top_iff hc, mul_left_comm (ENNReal.ofReal M) (ENNReal.ofReal c) S,
    HarmonicBalls.S11m.LocalRule.ennreal_mul_lt_mul_iff_of_ne hc0 hcT]

/-- **First event.** On the decoded data `DecodesOnSets`, the decoded first event holds iff the true `E₁`. -/
theorem decodedFirstCount_iff {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b : ℝ} (hb : 0 < b) (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ) (I : PinchCountSets V W T Q' Q δ)
    (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (ℓ : X) (hΦ : DecodesOnSets I Φ D b ℓ) :
    decodedFirstCount I Φ ℓ ↔ pinchFirstEventLocal D W T Q' Q δ := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := hΦ
  have hδ : 0 < δ := hgeo.delta_pos
  have hD' := hD.const_mul hb
  have hnn' : ∀ x y, 0 ≤ b * D x y := fun x y => mul_nonneg hb.le (hnn x y)
  have key : ∀ (O : Set ℂ) (x y : ℂ), ENNReal.ofReal b * internalMetric D O x y =
      internalMetric (fun x y => b * D x y) O x y := fun O x y => (internalMetric_const_mul D hb O x y).symm
  have eloc := S11ae.localFirstCount_congr (g := fun O x y => Φ O x y ℓ)
    (h := fun O x y => internalMetric (fun x y => b * D x y) O x y)
    (O := pinchOmegaGeom W Q δ) (Td := thickening δ (closure (T \ thickening (3 * δ) W)))
    (Sp := I.sp) (Qp := I.qp) (Fp := I.fp) (Cp := I.cp) (Ep := I.ep)
    (fun y hy => (h1 y hy).trans (key _ _ _)) (fun p hp q hq => (h2 p hp q hq).trans (key _ _ _))
    (fun x hx y hy => (h3 x hx y hy).trans (key _ _ _)) (fun p hp => (h4 p hp).trans (key _ _ _))
  have e2 : (⨅ p ∈ I.qp, ⨅ q ∈ I.fp, Φ univ p q ℓ) =
      ⨅ p ∈ I.qp, ⨅ q ∈ I.fp, internalMetric (fun x y => b * D x y) univ p q :=
    iInf_congr fun p => iInf_congr fun hp => iInf_congr fun q => iInf_congr fun hq =>
      (h2 p hp q hq).trans (key _ _ _)
  have e4 : (⨅ p ∈ I.ep, Φ univ 0 p ℓ) = ⨅ p ∈ I.ep, internalMetric (fun x y => b * D x y) univ 0 p :=
    iInf_congr fun p => iInf_congr fun hp => (h4 p hp).trans (key _ _ _)
  have hA : (closure Q').Nonempty := hgeo.isConnected_Q'.nonempty.closure
  have hB : (frontier Q).Nonempty := HarmonicBalls.S11m.IntRule.frontier_Q_nonempty hgeo
  have f2 : (⨅ p ∈ I.qp, ⨅ q ∈ I.fp, internalMetric (fun x y => b * D x y) univ p q) ≠ ⊤ := by
    rw [← ofReal_setDist_eq_countable hD' hA hB I.qp_dense.1 I.fp_dense.1 I.qp_dense.2.1 I.fp_dense.2.1]
    exact ENNReal.ofReal_ne_top
  have f4 : (⨅ p ∈ I.ep, internalMetric (fun x y => b * D x y) univ 0 p) ≠ ⊤ := by
    have h := ofReal_setDist_eq_countable hD' (singleton_nonempty (0 : ℂ))
      (NormedSpace.sphere_nonempty.mpr hδ.le) (subset_refl ({0} : Set ℂ)) I.ep_dense.1 subset_closure
      I.ep_dense.2.1
    have h' : ENNReal.ofReal (setDist (fun x y => b * D x y) {0} (sphere (0 : ℂ) δ)) =
        ⨅ p ∈ I.ep, internalMetric (fun x y => b * D x y) univ 0 p := by
      simpa only [Set.mem_singleton_iff, iInf_iInf_eq_left] using h
    rw [← h']
    exact ENNReal.ofReal_ne_top
  have hloc := (S11ae.pinchFirstEventLocal_iff_count hD' hnn' hgeo hΩ I.sp_dense.1 I.sp_dense.2.1 I.qp_dense.1
    I.qp_dense.2.1 I.fp_dense.1 I.fp_dense.2.1 I.cp_dense.1 I.cp_dense.2.1 I.ep_dense.1 I.ep_dense.2.1).symm.trans
    (HarmonicBalls.S11m.LocalRule.pinchFirstEventLocal_const_mul_iff D hb W T Q' Q δ)
  unfold decodedFirstCount
  rw [eloc, e2, e4]
  exact ⟨fun h => hloc.1 h.1, fun h => ⟨hloc.2 h, f2, f4⟩⟩

/-- **Second event.** On the decoded data `DecodesOnSets` and the decoded masses `c · S`, `c · μ(U)`, the decoded second
event holds iff the true `E₂(M)` holds and the two mass quantities are finite. -/
theorem decodedSecondCount_iff {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hδ : 0 < δ) (I : PinchCountSets V W T Q' Q δ)
    (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (mS mU : X → ℝ≥0∞) (μ : Measure ℂ) (M : ℝ) (ℓ : X)
    (hΦ : DecodesOnSets I Φ D b ℓ) (hmS : mS ℓ = ENNReal.ofReal c * annulusGreenPotentialSup μ 0 3 6)
    (hmU : mU ℓ = ENNReal.ofReal c * μ U) :
    decodedSecondCount I Φ mS mU M ℓ ↔
      pinchSecondEventLocal μ D U V δ M ∧ annulusGreenPotentialSup μ 0 3 6 ≠ ⊤ ∧ μ U ≠ ⊤ := by
  obtain ⟨-, -, -, -, h5, h6, -, -⟩ := hΦ
  have hD' := hD.const_mul hb
  have hnn' : ∀ x y, 0 ≤ b * D x y := fun x y => mul_nonneg hb.le (hnn x y)
  have key : ∀ (O : Set ℂ) (x y : ℂ), ENNReal.ofReal b * internalMetric D O x y =
      internalMetric (fun x y => b * D x y) O x y := fun O x y => (internalMetric_const_mul D hb O x y).symm
  have eloc := S11ae.localThirdCount_congr (g := fun O x y => Φ O x y ℓ)
    (h := fun O x y => internalMetric (fun x y => b * D x y) O x y)
    (Td := thickening δ (closure V)) (Sp2 := I.s2) (Sp3 := I.s3) (Cp := I.cv)
    (fun x hx y hy => (h5 x hx y hy).trans (key _ _ _)) (fun p hp q hq => (h6 p hp q hq).trans (key _ _ _))
  have e6 : (⨅ p ∈ I.s2, ⨅ q ∈ I.s3, Φ univ p q ℓ) =
      ⨅ p ∈ I.s2, ⨅ q ∈ I.s3, internalMetric (fun x y => b * D x y) univ p q :=
    iInf_congr fun p => iInf_congr fun hp => iInf_congr fun q => iInf_congr fun hq =>
      (h6 p hp q hq).trans (key _ _ _)
  have hb0 : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.2 hb).ne'
  have hbT : ENNReal.ofReal b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmet : internalDiam D δ (closure V) <
        ENNReal.ofReal (setDist D (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ))) ↔
      internalDiam (fun x y => b * D x y) δ (closure V) <
        ENNReal.ofReal (setDist (fun x y => b * D x y) (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ))) := by
    rw [HarmonicBalls.S11m.LocalRule.internalDiam_const_mul D hb, HarmonicBalls.S11n.setDist_smul_left hb.le D,
      ENNReal.ofReal_mul hb.le, HarmonicBalls.S11m.LocalRule.ennreal_mul_lt_mul_iff_of_ne hb0 hbT]
  have hsec := S11ag.secondMetric_iff_count hD' hnn' hδ V I.s2_dense.1 I.s2_dense.2.1 I.s3_dense.1
    I.s3_dense.2.1 I.cv_dense.1 I.cv_dense.2.1
  have hsecond := hsec.symm.trans hmet.symm
  have hfin : (⨅ p ∈ I.s2, ⨅ q ∈ I.s3, internalMetric (fun x y => b * D x y) univ p q) ≠ ⊤ := by
    rw [← ofReal_setDist_eq_countable hD' (NormedSpace.sphere_nonempty.mpr hδ.le)
      (NormedSpace.sphere_nonempty.mpr (by linarith : (0 : ℝ) ≤ 2 * δ)) I.s2_dense.1 I.s3_dense.1
      I.s2_dense.2.1 I.s3_dense.2.1]
    exact ENNReal.ofReal_ne_top
  have hmass : (mS ℓ ≠ ⊤ ∧ mU ℓ ≠ ⊤ ∧ ENNReal.ofReal M * mS ℓ < mU ℓ) ↔
      (annulusGreenPotentialSup μ 0 3 6 ≠ ⊤ ∧ μ U ≠ ⊤ ∧
        ENNReal.ofReal M * annulusGreenPotentialSup μ 0 3 6 < μ U) := by
    rw [hmS, hmU]
    exact mass_scaled_iff hc _ _
  unfold decodedSecondCount
  rw [eloc, e6, hmass]
  unfold pinchSecondEventLocal
  constructor
  · rintro ⟨hl, -, hS, hU, hlt⟩
    exact ⟨⟨hsecond.1 hl, hlt⟩, hS, hU⟩
  · rintro ⟨⟨hm, hlt⟩, hS, hU⟩
    exact ⟨hsecond.2 hm, hfin, hS, hU, hlt⟩

/-- **Third event.** On the decoded data `DecodesOnSets`, the decoded third event holds iff the true `E₃`. -/
theorem decodedThirdCount_iff {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b : ℝ} (hb : 0 < b) (hδ : 0 < δ) (I : PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞)
    (ℓ : X) (hΦ : DecodesOnSets I Φ D b ℓ) :
    decodedThirdCount I Φ ℓ ↔ pinchThirdEventLocal D V W δ := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := hΦ
  have hD' := hD.const_mul hb
  have hnn' : ∀ x y, 0 ≤ b * D x y := fun x y => mul_nonneg hb.le (hnn x y)
  have key : ∀ (O : Set ℂ) (x y : ℂ), ENNReal.ofReal b * internalMetric D O x y =
      internalMetric (fun x y => b * D x y) O x y := fun O x y => (internalMetric_const_mul D hb O x y).symm
  have eloc := S11ae.localThirdCount_congr (g := fun O x y => Φ O x y ℓ)
    (h := fun O x y => internalMetric (fun x y => b * D x y) O x y)
    (Td := thickening δ (closure (thickening (3 * δ) W \ V))) (Sp2 := I.t2) (Sp3 := I.t3) (Cp := I.ct)
    (fun x hx y hy => (h7 x hx y hy).trans (key _ _ _)) (fun p hp q hq => (h8 p hp q hq).trans (key _ _ _))
  have e8 : (⨅ p ∈ I.t2, ⨅ q ∈ I.t3, Φ univ p q ℓ) =
      ⨅ p ∈ I.t2, ⨅ q ∈ I.t3, internalMetric (fun x y => b * D x y) univ p q :=
    iInf_congr fun p => iInf_congr fun hp => iInf_congr fun q => iInf_congr fun hq =>
      (h8 p hp q hq).trans (key _ _ _)
  have f8 : (⨅ p ∈ I.t2, ⨅ q ∈ I.t3, internalMetric (fun x y => b * D x y) univ p q) ≠ ⊤ := by
    rw [← ofReal_setDist_eq_countable hD' (NormedSpace.sphere_nonempty.mpr (by linarith : (0 : ℝ) ≤ 2 * δ))
      (NormedSpace.sphere_nonempty.mpr (by linarith : (0 : ℝ) ≤ 3 * δ)) I.t2_dense.1 I.t3_dense.1
      I.t2_dense.2.1 I.t3_dense.2.1]
    exact ENNReal.ofReal_ne_top
  have hloc := (S11ae.pinchThirdEventLocal_iff_count hD' hnn' hδ V W I.t2_dense.1 I.t2_dense.2.1 I.t3_dense.1
    I.t3_dense.2.1 I.ct_dense.1 I.ct_dense.2.1).symm.trans
    (HarmonicBalls.S11m.LocalRule.pinchThirdEventLocal_const_mul_iff D hb V W δ)
  unfold decodedThirdCount
  rw [eloc, e8]
  exact ⟨fun h => hloc.1 h.1, fun h => ⟨hloc.2 h, f8⟩⟩

/-- **Identification of the decoded rule.** Let `D` be a Euclidean length metric and `μ` a measure. If at `ℓ` the decoded
metric is `b` times the internal metric of `D` on the countable point sets (`DecodesOnSets`) and the decoded masses are
`c` times the `μ`-masses (`0 < b`, `0 < c`), then `ℓ` lies in the decoded rule iff the true local certificate
`pinchLocalRule μ D` (equation (2)) holds and the two mass quantities `S = annulusGreenPotentialSup μ 0 3 6` and `μ(U)`
are finite. The finiteness conditions are exactly the rejection of nonfinite outputs. -/
theorem decodedPinchRule_iff {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ) (I : PinchCountSets V W T Q' Q δ)
    (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (mS mU : X → ℝ≥0∞) (μ : Measure ℂ) (M : ℝ) (ℓ : X)
    (hΦ : DecodesOnSets I Φ D b ℓ) (hmS : mS ℓ = ENNReal.ofReal c * annulusGreenPotentialSup μ 0 3 6)
    (hmU : mU ℓ = ENNReal.ofReal c * μ U) :
    ℓ ∈ decodedPinchRule I Φ mS mU M ↔
      HarmonicBalls.S11m.LocalRule.pinchLocalRule μ D W T Q' Q U V δ M ∧
        annulusGreenPotentialSup μ 0 3 6 ≠ ⊤ ∧ μ U ≠ ⊤ := by
  have hδ : 0 < δ := hgeo.delta_pos
  unfold decodedPinchRule
  show decodedFirstCount I Φ ℓ ∧ decodedSecondCount I Φ mS mU M ℓ ∧ decodedThirdCount I Φ ℓ ↔ _
  rw [decodedFirstCount_iff hD hnn hb hgeo hΩ I Φ ℓ hΦ,
    decodedSecondCount_iff hD hnn hb hc hδ I Φ mS mU μ M ℓ hΦ hmS hmU,
    decodedThirdCount_iff hD hnn hb hδ I Φ ℓ hΦ]
  unfold HarmonicBalls.S11m.LocalRule.pinchLocalRule
  tauto

end HarmonicBalls.S11am
