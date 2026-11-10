import HarmonicBalls.FirstPass.S11am
import HarmonicBalls.FirstPass.S11m.IntRule
import HarmonicBalls.FirstPass.S11m.DenseInf
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-!
# Decoded local rule on bounded domains (fp-S11ax, owner z7)

Interface fix requested by z4 (`reports/z4.md`, "INTERFACE FINDING"): the decoder only gives internal distances on
domains inside a bounded ball (`S11m/DecodedDomain.lean`), so the whole-plane values `Φ univ p q ℓ` of
`FirstPass/S11am.lean` are not available. The local events in their internal form (`FirstPass/S11m/IntRule.lean`) use
only bounded domains:

* `B₆` for the exit distance `L` (`pinchFirstEventInt`),
* `pinchOmegaGeom W Q δ` for the sup `A` (`pinchLocalA`),
* `B_{4δ}` for the crossing distances `a₀, a₁, a₂` (`pinchFirstEventInt`, `pinchSecondEventInt`, `pinchThirdEventInt`),
* the `δ`-thickenings `thickening δ K` for the diameters `d₀, d₁, d₂` (`internalDiam`).

`DecodesOnSetsBall` states the decoded values on these domains, on the countable dense sets of `S11am.PinchCountSets`.
`decodedPinchRuleBall` is the decoded rule with the same five strict inequalities and finiteness conjuncts as
`S11am.decodedPinchRule`; `decodedPinchRule_iff_ball` identifies it with `pinchLocalRule μ D` (the same conclusion as
`S11am.decodedPinchRule_iff`). Every event is local: no event needs the whole-plane distance, so no locality input is
needed beyond the internal forms.

Countable reduction: a two-variable infimum of the internal metric over closed sets is replaced by a countable dense
subset, using joint continuity on `O × O` (`IsEuclideanLengthMetric.continuousOn_internalMetric_pair`) and the dense
replacement lemma `S11m.iInf_mem_eq_iInf_mem_of_dense_continuousOn` (`FirstPass/S11m/DenseInf.lean`).
-/

namespace HarmonicBalls.S11ax

open MeasureTheory Set Metric Filter
open scoped ENNReal

variable {X : Type*}
variable {U V W T Q' Q : Set ℂ} {δ : ℝ}

/-! ### Countable reduction of the internal infima -/

/-- An infimum over a product set is the iterated infimum. -/
theorem iInf_prod_mem_eq {α β : Type*} (g : α × β → ℝ≥0∞) (A : Set α) (B : Set β) :
    (⨅ t ∈ A ×ˢ B, g t) = ⨅ x ∈ A, ⨅ y ∈ B, g (x, y) := by
  refine le_antisymm (le_iInf₂ fun x hx => le_iInf₂ fun y hy => iInf₂_le (x, y) ⟨hx, hy⟩)
    (le_iInf₂ fun t ht => ?_)
  exact (iInf₂_le t.1 ht.1).trans (iInf₂_le t.2 ht.2)

/-- **Two-variable countable reduction** of the internal metric infimum on an open `O`: for `K₁, K₂ ⊆ O` and countable
dense `S₁ ⊆ K₁`, `S₂ ⊆ K₂`, the infimum over `K₁ × K₂` equals the infimum over `S₁ × S₂`. -/
theorem iInf_pair_countable {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) (hnn : ∀ x y, 0 ≤ E x y)
    {O : Set ℂ} (hO : IsOpen O) {K1 K2 S1 S2 : Set ℂ} (hK1 : K1 ⊆ O) (hK2 : K2 ⊆ O)
    (hS1 : S1 ⊆ K1) (hS2 : S2 ⊆ K2) (hK1c : K1 ⊆ closure S1) (hK2c : K2 ⊆ closure S2) :
    (⨅ x ∈ K1, ⨅ y ∈ K2, internalMetric E O x y) = ⨅ x ∈ S1, ⨅ y ∈ S2, internalMetric E O x y := by
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric E O p.1 p.2) (K1 ×ˢ K2) :=
    (hE.continuousOn_internalMetric_pair hnn hO).mono (prod_mono hK1 hK2)
  have hdense : K1 ×ˢ K2 ⊆ closure (S1 ×ˢ S2) := by
    rw [closure_prod_eq]
    exact prod_mono hK1c hK2c
  have key := HarmonicBalls.S11m.iInf_mem_eq_iInf_mem_of_dense_continuousOn hcont (prod_mono hS1 hS2) hdense
  exact (iInf_prod_mem_eq (fun p : ℂ × ℂ => internalMetric E O p.1 p.2) K1 K2).symm.trans
    (key.trans (iInf_prod_mem_eq (fun p : ℂ × ℂ => internalMetric E O p.1 p.2) S1 S2))

/-- **One-variable countable reduction** of the internal metric infimum from a fixed point `x0`. -/
theorem iInf_sphere_countable {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) (hnn : ∀ x y, 0 ≤ E x y)
    {O : Set ℂ} (hO : IsOpen O) (x0 : ℂ) {K S : Set ℂ} (hK : K ⊆ O) (hS : S ⊆ K) (hKc : K ⊆ closure S) :
    (⨅ y ∈ K, internalMetric E O x0 y) = ⨅ y ∈ S, internalMetric E O x0 y :=
  HarmonicBalls.S11m.iInf_mem_eq_iInf_mem_of_dense_continuousOn
    ((hE.continuousOn_internalMetric hnn hO x0).mono hK) hS hKc

/-- **Countable form of the sup `A`** on `pinchOmegaGeom`: the supremum over `sphere 0 5` of the internal metric from `0`
is the supremum over a countable dense subset. -/
theorem pinchLocalA_countable {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E) (hnn : ∀ x y, 0 ≤ E x y)
    {W Q : Set ℂ} {δ : ℝ} {Sp : Set ℂ} (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ) (hSp : Sp ⊆ sphere (0 : ℂ) 5)
    (hSpc : sphere (0 : ℂ) 5 ⊆ closure Sp) :
    pinchLocalA E W Q δ = ⨆ y ∈ Sp, internalMetric E (pinchOmegaGeom W Q δ) 0 y := by
  have hO : IsOpen (pinchOmegaGeom W Q δ) := HarmonicBalls.S11m.E1Bounds.pinchOmegaGeom_isOpen W Q δ
  unfold pinchLocalA
  exact iSup_eq_iSup_of_dense_of_continuousOn hO hΩ hSp hSpc (hE.continuousOn_internalMetric hnn hO 0)

/-- The sphere `∂B_r` lies in the open ball `B_R` for `r < R`. -/
theorem sphere_subset_ball_of_lt {r R : ℝ} (hrR : r < R) : sphere (0 : ℂ) r ⊆ ball (0 : ℂ) R := by
  intro x hx
  rw [mem_sphere_zero_iff_norm] at hx
  rw [mem_ball_zero_iff]
  linarith

/-! ### Decoded data on bounded domains -/

/-- **Decoded data on the bounded domains.** At `ℓ`, the decoded values equal `ofReal b` times the internal metric of `D`
on the countable point sets of `I`, on the domains of the internal local events: `pinchOmegaGeom` (sup `A`), `B₆` (exit
distance `L`), `B_{4δ}` (crossing distances `a₀, a₁, a₂`), and the δ-thickenings of the diameter sets `d₀, d₁, d₂`. -/
def DecodesOnSetsBall (I : S11am.PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞)
    (D : ℂ → ℂ → ℝ) (b : ℝ) (ℓ : X) : Prop :=
  (∀ y ∈ I.sp, Φ (pinchOmegaGeom W Q δ) 0 y ℓ =
      ENNReal.ofReal b * internalMetric D (pinchOmegaGeom W Q δ) 0 y) ∧
  (∀ p ∈ I.qp, ∀ q ∈ I.fp, Φ (ball (0 : ℂ) 6) p q ℓ = ENNReal.ofReal b * internalMetric D (ball (0 : ℂ) 6) p q) ∧
  (∀ x ∈ I.cp, ∀ y ∈ I.cp, Φ (thickening δ (closure (T \ thickening (3 * δ) W))) x y ℓ =
      ENNReal.ofReal b * internalMetric D (thickening δ (closure (T \ thickening (3 * δ) W))) x y) ∧
  (∀ p ∈ I.ep, Φ (ball (0 : ℂ) (4 * δ)) 0 p ℓ = ENNReal.ofReal b * internalMetric D (ball (0 : ℂ) (4 * δ)) 0 p) ∧
  (∀ x ∈ I.cv, ∀ y ∈ I.cv, Φ (thickening δ (closure V)) x y ℓ =
      ENNReal.ofReal b * internalMetric D (thickening δ (closure V)) x y) ∧
  (∀ p ∈ I.s2, ∀ q ∈ I.s3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ =
      ENNReal.ofReal b * internalMetric D (ball (0 : ℂ) (4 * δ)) p q) ∧
  (∀ x ∈ I.ct, ∀ y ∈ I.ct, Φ (thickening δ (closure (thickening (3 * δ) W \ V))) x y ℓ =
      ENNReal.ofReal b * internalMetric D (thickening δ (closure (thickening (3 * δ) W \ V))) x y) ∧
  (∀ p ∈ I.t2, ∀ q ∈ I.t3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ =
      ENNReal.ofReal b * internalMetric D (ball (0 : ℂ) (4 * δ)) p q)

/-- Decoded first local event on the bounded domains: the countable form of `pinchFirstEventInt`, with the two infima
(right sides) finite. -/
def decodedFirstCountBall (I : S11am.PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (ℓ : X) : Prop :=
  (⨆ y ∈ I.sp, Φ (pinchOmegaGeom W Q δ) 0 y ℓ) < (⨅ p ∈ I.qp, ⨅ q ∈ I.fp, Φ (ball (0 : ℂ) 6) p q ℓ) ∧
    (⨆ x ∈ I.cp, ⨆ y ∈ I.cp, Φ (thickening δ (closure (T \ thickening (3 * δ) W))) x y ℓ) <
      (⨅ p ∈ I.ep, Φ (ball (0 : ℂ) (4 * δ)) 0 p ℓ) ∧
  (⨅ p ∈ I.qp, ⨅ q ∈ I.fp, Φ (ball (0 : ℂ) 6) p q ℓ) ≠ ⊤ ∧
    (⨅ p ∈ I.ep, Φ (ball (0 : ℂ) (4 * δ)) 0 p ℓ) ≠ ⊤

/-- Decoded second local event on the bounded domains: the countable metric clause with finite right side, and the mass
clause on the decoded masses (both finite). -/
def decodedSecondCountBall (I : S11am.PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞)
    (mS mU : X → ℝ≥0∞) (M : ℝ) (ℓ : X) : Prop :=
  (⨆ x ∈ I.cv, ⨆ y ∈ I.cv, Φ (thickening δ (closure V)) x y ℓ) <
      (⨅ p ∈ I.s2, ⨅ q ∈ I.s3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ) ∧
    (⨅ p ∈ I.s2, ⨅ q ∈ I.s3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ) ≠ ⊤ ∧
    (mS ℓ ≠ ⊤ ∧ mU ℓ ≠ ⊤ ∧ ENNReal.ofReal M * mS ℓ < mU ℓ)

/-- Decoded third local event on the bounded domains: the countable form of `pinchThirdEventInt`, with finite right
side. -/
def decodedThirdCountBall (I : S11am.PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (ℓ : X) : Prop :=
  (⨆ x ∈ I.ct, ⨆ y ∈ I.ct, Φ (thickening δ (closure (thickening (3 * δ) W \ V))) x y ℓ) <
      (⨅ p ∈ I.t2, ⨅ q ∈ I.t3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ) ∧
    (⨅ p ∈ I.t2, ⨅ q ∈ I.t3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ) ≠ ⊤

/-- The decoded local rule `E₁ ∩ E₂(M) ∩ E₃` on the bounded domains (route section 5: nonfinite outputs rejected). -/
def decodedPinchRuleBall (I : S11am.PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞)
    (mS mU : X → ℝ≥0∞) (M : ℝ) : Set X :=
  {ℓ | decodedFirstCountBall I Φ ℓ ∧ decodedSecondCountBall I Φ mS mU M ℓ ∧ decodedThirdCountBall I Φ ℓ}

/-! ### Identification with the true local rule -/

/-- **First event on bounded domains.** Under `DecodesOnSetsBall`, the decoded first event holds iff the internal first
event `pinchFirstEventInt D` holds. -/
theorem decodedFirstCountBall_iff {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b : ℝ} (hb : 0 < b) (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ) (I : S11am.PinchCountSets V W T Q' Q δ)
    (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (ℓ : X) (hΦ : DecodesOnSetsBall I Φ D b ℓ) :
    decodedFirstCountBall I Φ ℓ ↔ HarmonicBalls.S11m.IntRule.pinchFirstEventInt D W T Q' Q δ := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := hΦ
  have hδ : 0 < δ := hgeo.delta_pos
  have hD' := hD.const_mul hb
  have hnn' : ∀ x y, 0 ≤ b * D x y := fun x y => mul_nonneg hb.le (hnn x y)
  have key : ∀ (O : Set ℂ) (x y : ℂ), ENNReal.ofReal b * internalMetric D O x y =
      internalMetric (fun x y => b * D x y) O x y := fun O x y => (internalMetric_const_mul D hb O x y).symm
  have e1 : (⨆ y ∈ I.sp, Φ (pinchOmegaGeom W Q δ) 0 y ℓ) =
      ⨆ y ∈ I.sp, internalMetric (fun x y => b * D x y) (pinchOmegaGeom W Q δ) 0 y :=
    iSup_congr fun y => iSup_congr fun hy => (h1 y hy).trans (key _ _ _)
  have e2 : (⨅ p ∈ I.qp, ⨅ q ∈ I.fp, Φ (ball (0 : ℂ) 6) p q ℓ) =
      ⨅ p ∈ I.qp, ⨅ q ∈ I.fp, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) 6) p q :=
    iInf_congr fun p => iInf_congr fun hp => iInf_congr fun q => iInf_congr fun hq =>
      (h2 p hp q hq).trans (key _ _ _)
  have e3 : (⨆ x ∈ I.cp, ⨆ y ∈ I.cp, Φ (thickening δ (closure (T \ thickening (3 * δ) W))) x y ℓ) =
      ⨆ x ∈ I.cp, ⨆ y ∈ I.cp,
        internalMetric (fun x y => b * D x y) (thickening δ (closure (T \ thickening (3 * δ) W))) x y :=
    iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy =>
      (h3 x hx y hy).trans (key _ _ _)
  have e4 : (⨅ p ∈ I.ep, Φ (ball (0 : ℂ) (4 * δ)) 0 p ℓ) =
      ⨅ p ∈ I.ep, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) (4 * δ)) 0 p :=
    iInf_congr fun p => iInf_congr fun hp => (h4 p hp).trans (key _ _ _)
  have hA := pinchLocalA_countable hD' hnn' hΩ I.sp_dense.1 I.sp_dense.2.1
  have hcl6 : closure Q' ⊆ ball (0 : ℂ) 6 :=
    (hgeo.closure_Q'_subset_Q.trans subset_closure).trans (HarmonicBalls.S11m.IntRule.closure_Q_subset_ball_six hgeo)
  have hfr6 : frontier Q ⊆ ball (0 : ℂ) 6 :=
    frontier_subset_closure.trans (HarmonicBalls.S11m.IntRule.closure_Q_subset_ball_six hgeo)
  have hL := iInf_pair_countable hD' hnn' isOpen_ball hcl6 hfr6 I.qp_dense.1 I.fp_dense.1 I.qp_dense.2.1
    I.fp_dense.2.1
  have hd0 := internalDiam_eq_countable hD' hnn' hδ I.cp_dense.1 I.cp_dense.2.1
  have ha0 := iInf_sphere_countable hD' hnn' isOpen_ball 0 (sphere_subset_ball_of_lt (by linarith : δ < 4 * δ))
    I.ep_dense.1 I.ep_dense.2.1
  have hfin1 : (⨅ p ∈ I.qp, ⨅ q ∈ I.fp, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) 6) p q) ≠ ⊤ := by
    rw [← hL, ← HarmonicBalls.S11m.IntRule.ofReal_pinchLocalL_eq_internal hD' hgeo]
    exact ENNReal.ofReal_ne_top
  have hfin2 : (⨅ p ∈ I.ep, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) (4 * δ)) 0 p) ≠ ⊤ := by
    rw [← ha0, ← HarmonicBalls.S11m.IntRule.ofReal_setDist_origin_eq_internal hD' hδ]
    exact ENNReal.ofReal_ne_top
  have hcount : decodedFirstCountBall I Φ ℓ ↔
      HarmonicBalls.S11m.IntRule.pinchFirstEventInt (fun x y => b * D x y) W T Q' Q δ := by
    unfold decodedFirstCountBall HarmonicBalls.S11m.IntRule.pinchFirstEventInt
    rw [e1, e2, e3, e4, hA, hL, hd0, ha0]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hfin1, hfin2⟩⟩
  exact hcount.trans (HarmonicBalls.S11m.IntRule.pinchFirstEventInt_const_mul_iff D hb W T Q' Q δ)

/-- **Second event on bounded domains.** Under `DecodesOnSetsBall` and decoded masses `c · S`, `c · μ(U)`, the decoded
second event holds iff the internal second event `pinchSecondEventInt μ D` holds and the two masses are finite. -/
theorem decodedSecondCountBall_iff {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hδ : 0 < δ) (I : S11am.PinchCountSets V W T Q' Q δ)
    (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (mS mU : X → ℝ≥0∞) (μ : Measure ℂ) (M : ℝ) (ℓ : X)
    (hΦ : DecodesOnSetsBall I Φ D b ℓ) (hmS : mS ℓ = ENNReal.ofReal c * annulusGreenPotentialSup μ 0 3 6)
    (hmU : mU ℓ = ENNReal.ofReal c * μ U) :
    decodedSecondCountBall I Φ mS mU M ℓ ↔
      HarmonicBalls.S11m.IntRule.pinchSecondEventInt μ D U V δ M ∧
        annulusGreenPotentialSup μ 0 3 6 ≠ ⊤ ∧ μ U ≠ ⊤ := by
  obtain ⟨-, -, -, -, h5, h6, -, -⟩ := hΦ
  have hD' := hD.const_mul hb
  have hnn' : ∀ x y, 0 ≤ b * D x y := fun x y => mul_nonneg hb.le (hnn x y)
  have key : ∀ (O : Set ℂ) (x y : ℂ), ENNReal.ofReal b * internalMetric D O x y =
      internalMetric (fun x y => b * D x y) O x y := fun O x y => (internalMetric_const_mul D hb O x y).symm
  have e5 : (⨆ x ∈ I.cv, ⨆ y ∈ I.cv, Φ (thickening δ (closure V)) x y ℓ) =
      ⨆ x ∈ I.cv, ⨆ y ∈ I.cv, internalMetric (fun x y => b * D x y) (thickening δ (closure V)) x y :=
    iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy =>
      (h5 x hx y hy).trans (key _ _ _)
  have e6 : (⨅ p ∈ I.s2, ⨅ q ∈ I.s3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ) =
      ⨅ p ∈ I.s2, ⨅ q ∈ I.s3, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) (4 * δ)) p q :=
    iInf_congr fun p => iInf_congr fun hp => iInf_congr fun q => iInf_congr fun hq =>
      (h6 p hp q hq).trans (key _ _ _)
  have hd1 := internalDiam_eq_countable hD' hnn' hδ I.cv_dense.1 I.cv_dense.2.1
  have ha1 := iInf_pair_countable hD' hnn' isOpen_ball
    (sphere_subset_ball_of_lt (by linarith : δ < 4 * δ)) (sphere_subset_ball_of_lt (by linarith : 2 * δ < 4 * δ))
    I.s2_dense.1 I.s3_dense.1 I.s2_dense.2.1 I.s3_dense.2.1
  have hfin : (⨅ p ∈ I.s2, ⨅ q ∈ I.s3, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) (4 * δ)) p q) ≠ ⊤ := by
    rw [← ha1, ← HarmonicBalls.S11m.IntRule.ofReal_setDist_sphere_eq_internal hD' hδ]
    exact ENNReal.ofReal_ne_top
  have hscal : HarmonicBalls.S11m.IntRule.pinchSecondEventInt μ (fun x y => b * D x y) U V δ M ↔
      HarmonicBalls.S11m.IntRule.pinchSecondEventInt μ D U V δ M := by
    have h := HarmonicBalls.S11m.IntRule.pinchSecondEventInt_smul_iff μ D (a := 1) zero_lt_one hb U V δ M
    rwa [ENNReal.ofReal_one, one_smul] at h
  have hcount : decodedSecondCountBall I Φ mS mU M ℓ ↔
      HarmonicBalls.S11m.IntRule.pinchSecondEventInt μ (fun x y => b * D x y) U V δ M ∧
        annulusGreenPotentialSup μ 0 3 6 ≠ ⊤ ∧ μ U ≠ ⊤ := by
    unfold decodedSecondCountBall HarmonicBalls.S11m.IntRule.pinchSecondEventInt
    rw [e5, e6, hd1, ha1, hmS, hmU, S11am.mass_scaled_iff hc]
    constructor
    · rintro ⟨hl, -, hS, hU', hlt⟩
      exact ⟨⟨hl, hlt⟩, hS, hU'⟩
    · rintro ⟨⟨hl, hlt⟩, hS, hU'⟩
      exact ⟨hl, hfin, hS, hU', hlt⟩
  rw [hcount, hscal]

/-- **Third event on bounded domains.** Under `DecodesOnSetsBall`, the decoded third event holds iff the internal third
event `pinchThirdEventInt D` holds. -/
theorem decodedThirdCountBall_iff {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b : ℝ} (hb : 0 < b) (hδ : 0 < δ) (I : S11am.PinchCountSets V W T Q' Q δ) (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞)
    (ℓ : X) (hΦ : DecodesOnSetsBall I Φ D b ℓ) :
    decodedThirdCountBall I Φ ℓ ↔ HarmonicBalls.S11m.IntRule.pinchThirdEventInt D V W δ := by
  obtain ⟨-, -, -, -, -, -, h7, h8⟩ := hΦ
  have hD' := hD.const_mul hb
  have hnn' : ∀ x y, 0 ≤ b * D x y := fun x y => mul_nonneg hb.le (hnn x y)
  have key : ∀ (O : Set ℂ) (x y : ℂ), ENNReal.ofReal b * internalMetric D O x y =
      internalMetric (fun x y => b * D x y) O x y := fun O x y => (internalMetric_const_mul D hb O x y).symm
  have e7 : (⨆ x ∈ I.ct, ⨆ y ∈ I.ct, Φ (thickening δ (closure (thickening (3 * δ) W \ V))) x y ℓ) =
      ⨆ x ∈ I.ct, ⨆ y ∈ I.ct,
        internalMetric (fun x y => b * D x y) (thickening δ (closure (thickening (3 * δ) W \ V))) x y :=
    iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy =>
      (h7 x hx y hy).trans (key _ _ _)
  have e8 : (⨅ p ∈ I.t2, ⨅ q ∈ I.t3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ) =
      ⨅ p ∈ I.t2, ⨅ q ∈ I.t3, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) (4 * δ)) p q :=
    iInf_congr fun p => iInf_congr fun hp => iInf_congr fun q => iInf_congr fun hq =>
      (h8 p hp q hq).trans (key _ _ _)
  have hd2 := internalDiam_eq_countable hD' hnn' hδ I.ct_dense.1 I.ct_dense.2.1
  have ha2 := iInf_pair_countable hD' hnn' isOpen_ball
    (sphere_subset_ball_of_lt (by linarith : 2 * δ < 4 * δ)) (sphere_subset_ball_of_lt (by linarith : 3 * δ < 4 * δ))
    I.t2_dense.1 I.t3_dense.1 I.t2_dense.2.1 I.t3_dense.2.1
  have hfin : (⨅ p ∈ I.t2, ⨅ q ∈ I.t3, internalMetric (fun x y => b * D x y) (ball (0 : ℂ) (4 * δ)) p q) ≠ ⊤ := by
    rw [← ha2, ← HarmonicBalls.S11m.IntRule.ofReal_setDist_outer_eq_internal hD' hδ]
    exact ENNReal.ofReal_ne_top
  have hcount : decodedThirdCountBall I Φ ℓ ↔
      HarmonicBalls.S11m.IntRule.pinchThirdEventInt (fun x y => b * D x y) V W δ := by
    unfold decodedThirdCountBall HarmonicBalls.S11m.IntRule.pinchThirdEventInt
    rw [e7, e8, hd2, ha2]
    exact ⟨fun h => h.1, fun h => ⟨h, hfin⟩⟩
  exact hcount.trans (HarmonicBalls.S11m.IntRule.pinchThirdEventInt_const_mul_iff D hb V W δ)

/-- **Identification of the decoded rule on bounded domains.** Let `D` be a Euclidean length metric and `μ` a measure.
If at `ℓ` the decoded values are `b` times the internal metric of `D` on the countable point sets (`DecodesOnSetsBall`)
and the decoded masses are `c` times the `μ`-masses (`0 < b`, `0 < c`), then `ℓ` lies in the decoded rule iff the true
local certificate `pinchLocalRule μ D` (equation (2)) holds and the two mass quantities are finite. -/
theorem decodedPinchRule_iff_ball {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnn : ∀ x y, 0 ≤ D x y)
    {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ) (I : S11am.PinchCountSets V W T Q' Q δ)
    (Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞) (mS mU : X → ℝ≥0∞) (μ : Measure ℂ) (M : ℝ) (ℓ : X)
    (hΦ : DecodesOnSetsBall I Φ D b ℓ) (hmS : mS ℓ = ENNReal.ofReal c * annulusGreenPotentialSup μ 0 3 6)
    (hmU : mU ℓ = ENNReal.ofReal c * μ U) :
    ℓ ∈ decodedPinchRuleBall I Φ mS mU M ↔
      HarmonicBalls.S11m.LocalRule.pinchLocalRule μ D W T Q' Q U V δ M ∧
        annulusGreenPotentialSup μ 0 3 6 ≠ ⊤ ∧ μ U ≠ ⊤ := by
  have hδ : 0 < δ := hgeo.delta_pos
  show decodedFirstCountBall I Φ ℓ ∧ decodedSecondCountBall I Φ mS mU M ℓ ∧ decodedThirdCountBall I Φ ℓ ↔ _
  rw [decodedFirstCountBall_iff hD hnn hb hgeo hΩ I Φ ℓ hΦ,
    decodedSecondCountBall_iff hD hnn hb hc hδ I Φ mS mU μ M ℓ hΦ hmS hmU,
    decodedThirdCountBall_iff hD hnn hb hδ I Φ ℓ hΦ,
    HarmonicBalls.S11m.IntRule.pinchLocalRule_iff_int hD hgeo μ M]
  unfold HarmonicBalls.S11m.IntRule.pinchLocalRuleInt
  tauto

/-! ### Measurability on bounded domains -/

/-- The decoded first event on bounded domains is measurable, for measurable decoders on open domains. -/
theorem measurableSet_decodedFirstCountBall [MeasurableSpace X] (I : S11am.PinchCountSets V W T Q' Q δ)
    {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞} (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ) :
    MeasurableSet {ℓ | decodedFirstCountBall I Φ ℓ} := by
  have hO : IsOpen (pinchOmegaGeom W Q δ) := HarmonicBalls.S11m.E1Bounds.pinchOmegaGeom_isOpen W Q δ
  have m1 : Measurable fun ℓ => ⨆ y ∈ I.sp, Φ (pinchOmegaGeom W Q δ) 0 y ℓ :=
    measurable_iSup_mem_of_countable I.sp_dense.2.2 fun y => hΦ _ hO 0 y
  have m2 : Measurable fun ℓ => ⨅ p ∈ I.qp, ⨅ q ∈ I.fp, Φ (ball (0 : ℂ) 6) p q ℓ :=
    measurable_iInf_mem_of_countable I.qp_dense.2.2 fun p =>
      measurable_iInf_mem_of_countable I.fp_dense.2.2 fun q => hΦ _ isOpen_ball p q
  have m3 : Measurable fun ℓ =>
      ⨆ x ∈ I.cp, ⨆ y ∈ I.cp, Φ (thickening δ (closure (T \ thickening (3 * δ) W))) x y ℓ :=
    measurable_iSup_mem_of_countable I.cp_dense.2.2 fun x =>
      measurable_iSup_mem_of_countable I.cp_dense.2.2 fun y => hΦ _ isOpen_thickening x y
  have m4 : Measurable fun ℓ => ⨅ p ∈ I.ep, Φ (ball (0 : ℂ) (4 * δ)) 0 p ℓ :=
    measurable_iInf_mem_of_countable I.ep_dense.2.2 fun p => hΦ _ isOpen_ball 0 p
  exact (measurableSet_lt m1 m2).inter ((measurableSet_lt m3 m4).inter
    ((S11am.measurableSet_ne_top_of m2).inter (S11am.measurableSet_ne_top_of m4)))

/-- The decoded second event on bounded domains is measurable, for measurable decoders and masses. -/
theorem measurableSet_decodedSecondCountBall [MeasurableSpace X] (I : S11am.PinchCountSets V W T Q' Q δ)
    {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞} (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ)
    {mS mU : X → ℝ≥0∞} (hmS : Measurable mS) (hmU : Measurable mU) (M : ℝ) :
    MeasurableSet {ℓ | decodedSecondCountBall I Φ mS mU M ℓ} := by
  have m1 : Measurable fun ℓ => ⨆ x ∈ I.cv, ⨆ y ∈ I.cv, Φ (thickening δ (closure V)) x y ℓ :=
    measurable_iSup_mem_of_countable I.cv_dense.2.2 fun x =>
      measurable_iSup_mem_of_countable I.cv_dense.2.2 fun y => hΦ _ isOpen_thickening x y
  have m2 : Measurable fun ℓ => ⨅ p ∈ I.s2, ⨅ q ∈ I.s3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ :=
    measurable_iInf_mem_of_countable I.s2_dense.2.2 fun p =>
      measurable_iInf_mem_of_countable I.s3_dense.2.2 fun q => hΦ _ isOpen_ball p q
  have hmass : MeasurableSet {ℓ | mS ℓ ≠ ⊤ ∧ mU ℓ ≠ ⊤ ∧ ENNReal.ofReal M * mS ℓ < mU ℓ} :=
    (S11am.measurableSet_ne_top_of hmS).inter
      ((S11am.measurableSet_ne_top_of hmU).inter (measurableSet_lt (hmS.const_mul _) hmU))
  exact (measurableSet_lt m1 m2).inter ((S11am.measurableSet_ne_top_of m2).inter hmass)

/-- The decoded third event on bounded domains is measurable, for measurable decoders on open domains. -/
theorem measurableSet_decodedThirdCountBall [MeasurableSpace X] (I : S11am.PinchCountSets V W T Q' Q δ)
    {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞} (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ) :
    MeasurableSet {ℓ | decodedThirdCountBall I Φ ℓ} := by
  have m1 : Measurable fun ℓ =>
      ⨆ x ∈ I.ct, ⨆ y ∈ I.ct, Φ (thickening δ (closure (thickening (3 * δ) W \ V))) x y ℓ :=
    measurable_iSup_mem_of_countable I.ct_dense.2.2 fun x =>
      measurable_iSup_mem_of_countable I.ct_dense.2.2 fun y => hΦ _ isOpen_thickening x y
  have m2 : Measurable fun ℓ => ⨅ p ∈ I.t2, ⨅ q ∈ I.t3, Φ (ball (0 : ℂ) (4 * δ)) p q ℓ :=
    measurable_iInf_mem_of_countable I.t2_dense.2.2 fun p =>
      measurable_iInf_mem_of_countable I.t3_dense.2.2 fun q => hΦ _ isOpen_ball p q
  exact (measurableSet_lt m1 m2).inter (S11am.measurableSet_ne_top_of m2)

/-- **Measurability of the decoded rule on bounded domains.** -/
theorem measurableSet_decodedPinchRuleBall [MeasurableSpace X] (I : S11am.PinchCountSets V W T Q' Q δ)
    {Φ : Set ℂ → ℂ → ℂ → X → ℝ≥0∞} (hΦ : ∀ O : Set ℂ, IsOpen O → ∀ x y : ℂ, Measurable fun ℓ => Φ O x y ℓ)
    {mS mU : X → ℝ≥0∞} (hmS : Measurable mS) (hmU : Measurable mU) (M : ℝ) :
    MeasurableSet (decodedPinchRuleBall I Φ mS mU M) :=
  (measurableSet_decodedFirstCountBall I hΦ).inter
    ((measurableSet_decodedSecondCountBall I hΦ hmS hmU M).inter (measurableSet_decodedThirdCountBall I hΦ))

end HarmonicBalls.S11ax
