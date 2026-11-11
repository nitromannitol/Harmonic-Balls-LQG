import HarmonicBalls.FirstPass.S11m.ClearanceEq
import HarmonicBalls.Steps.Sec11.MetricConstantScaling

/-!
# Decoded localized clearance is a positive multiple of the internal metric

Route: internalization by countable clearance chains (identity L-EQ of `FirstPass/S11m/ClearanceEq.lean`); one scale factor per decoded quantity.

A metric decoder on the punctured ball `V = B_R \ {0}` returns, almost surely, a positive random multiple `c` of the
internal metric of `V`. This file shows that the localized clearance infimum computed from such a decoded cost is
`c · internalMetric D O` on an open `O ⊆ V`. Deterministic; no probability and no inputs beyond a Euclidean length
metric `D`.
-/

namespace HarmonicBalls.S11m

open Set Metric MeasureTheory
open scoped ENNReal

/-- Scaling a Euclidean length metric by `c > 0` gives a Euclidean length metric (lengths and the internal metric
of `ℂ` scale by `c`; the `D`-open sets are unchanged). -/
theorem isEuclideanLengthMetric_const_mul {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {c : ℝ} (hc : 0 < c) :
    IsEuclideanLengthMetric (fun x y => c * D x y) where
  self_eq_zero z := by
    show c * D z z = 0
    rw [hD.self_eq_zero z, mul_zero]
  eq_of_eq_zero z w h := by
    apply hD.eq_of_eq_zero z w
    exact (mul_eq_zero.1 h).resolve_left hc.ne'
  symm z w := by
    show c * D z w = c * D w z
    rw [hD.symm z w]
  triangle x y z := by
    show c * D x z ≤ c * D x y + c * D y z
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (hD.triangle x y z) hc.le
  isOpen_iff U := by
    rw [hD.isOpen_iff U]
    constructor
    · intro h z hz
      obtain ⟨ε, hε, hball⟩ := h z hz
      refine ⟨c * ε, mul_pos hc hε, fun w hw => hball w ?_⟩
      exact lt_of_mul_lt_mul_left hw hc.le
    · intro h z hz
      obtain ⟨ε, hε, hball⟩ := h z hz
      refine ⟨ε / c, div_pos hε hc, fun w hw => hball w ?_⟩
      rw [mul_comm]
      exact (lt_div_iff₀ hc).1 hw
  ofReal_eq_internalMetric z w := by
    show ENNReal.ofReal (c * D z w) = internalMetric (fun x y => c * D x y) univ z w
    rw [ENNReal.ofReal_mul hc.le, hD.ofReal_eq_internalMetric z w, internalMetric_const_mul D hc]

/-- The localized clearance infimum reads the cost only on `V × V`, when the interior vertex set `S` and the clearance
set `Q` lie in `V` and the endpoints lie in `V`. -/
theorem localClearanceInf_congr_of_eqOn {S Q V : Set ℂ} (hSV : S ⊆ V) (hQV : Q ⊆ V) {D₁ D₂ : ℂ → ℂ → ℝ}
    (hEq : ∀ v ∈ V, ∀ w ∈ V, D₁ v w = D₂ v w) {x y : ℂ} (hx : x ∈ V) (hy : y ∈ V) :
    localClearanceInf S Q D₁ x y = localClearanceInf S Q D₂ x y := by
  unfold localClearanceInf
  refine iInf_congr fun k => ?_
  have hv : ∀ i, denseChainVertex x y k i ∈ V := fun i => denseChainVertex_mem hSV hx hy k
  have hedge : ∀ i, D₁ (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) =
      D₂ (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) :=
    fun i => hEq _ (hv i) _ (hv (i + 1))
  have hclear : ∀ i, ∀ q ∈ Q, D₁ (denseChainVertex x y k i) q = D₂ (denseChainVertex x y k i) q :=
    fun i q hq => hEq _ (hv i) _ (hQV hq)
  have hcond : (∀ i < k.1 + 1, ∃ δ : ℚ, 0 < δ ∧
      D₁ (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ) ∧
      ∀ q ∈ Q, (δ : ℝ) ≤ D₁ (denseChainVertex x y k i) q) ↔
      (∀ i < k.1 + 1, ∃ δ : ℚ, 0 < δ ∧
      D₂ (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ) ∧
      ∀ q ∈ Q, (δ : ℝ) ≤ D₂ (denseChainVertex x y k i) q) :=
    forall_congr' fun i => imp_congr_right fun _ => exists_congr fun δ => and_congr_right fun _ =>
      and_congr (by rw [hedge i]) (forall_congr' fun q => imp_congr_right fun hq => by rw [hclear i q hq])
  unfold localClearanceCost
  split_ifs with h1 h2 h2
  · exact Finset.sum_congr rfl fun i _ => by rw [hedge i]
  · exact absurd (hcond.1 h1) h2
  · exact absurd (hcond.2 h2) h1
  · rfl

/-- **Decoded clearance identity.** If `Dh` equals `c · internalCost D V` on `V × V` for a constant `c > 0`, then the
localized clearance infimum of `Dh` between points of `O` is `c · internalMetric D O` (route section 4.3, L-EQ, with the
scale factor of section 5). The sets satisfy the hypotheses of `localClearanceInf_eq_internalMetric`. -/
theorem localClearanceInf_eq_const_mul_internalMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {V O S Q : Set ℂ} (hO : IsOpen O) (hVo : IsOpen V) (hOV : O ⊆ V) (hSV : S ⊆ V) (hS : O ⊆ closure S)
    (hQV : Q ⊆ V \ O) (hQd : V \ O ⊆ closure Q) (hfin : ∀ v ∈ V, ∀ w ∈ V, internalMetric D V v w ≠ ⊤)
    {c : ℝ} (hc : 0 < c) {Dh : ℂ → ℂ → ℝ}
    (hDh : ∀ v ∈ V, ∀ w ∈ V, Dh v w = c * internalCost D V v w) {x y : ℂ} (hx : x ∈ O) (hy : y ∈ O) :
    localClearanceInf S Q Dh x y = ENNReal.ofReal c * internalMetric D O x y := by
  have hD' := isEuclideanLengthMetric_const_mul hD hc
  have hfin' : ∀ v ∈ V, ∀ w ∈ V, internalMetric (fun u v => c * D u v) V v w ≠ ⊤ := fun v hv w hw => by
    rw [internalMetric_const_mul D hc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin v hv w hw)
  have hcost : ∀ v ∈ V, ∀ w ∈ V, Dh v w = internalCost (fun u v => c * D u v) V v w := fun v hv w hw => by
    rw [hDh v hv w hw]
    unfold internalCost
    rw [internalMetric_const_mul D hc, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc.le]
  have hxV : x ∈ V := hOV hx
  have hyV : y ∈ V := hOV hy
  rw [localClearanceInf_congr_of_eqOn hSV (hQV.trans sdiff_subset) hcost hxV hyV,
    localClearanceInf_eq_internalMetric hD' hO hVo hOV hSV hS hQV hQd hfin' hx hy,
    internalMetric_const_mul D hc]

end HarmonicBalls.S11m
