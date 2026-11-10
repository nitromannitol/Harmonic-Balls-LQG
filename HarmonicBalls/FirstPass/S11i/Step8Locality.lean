import Mathlib
import HarmonicBalls.Steps.Sec11.ApproximatePaths
import HarmonicBalls.Steps.Sec11.PinchInequalities

/-!
# Locality of the internal metric on a cutoff ball (Step 8, fp-S11i-11-13f, n3)

Source: Bou-Rabee-Gwynne, `paper/lqg_harmonic_ball-corrected.tex` l.3410-3420 (the internal-metric remark in the
certificate section): in a length metric inducing the Euclidean topology, nearly shortest paths between points of a
smaller ball cannot leave the larger one, so the internal and ambient metrics agree locally (Armstrong-Kuusi-Mourrat
terminology: internal metric `D(·,·; O)` of a Euclidean-open `O`).

* `internalMetric_eq_ofReal_of_gap`: if `x, y` are at `D`-distance at least `r` from the complement of `O` and
  `D x y < 2 r`, the internal metric of `O` equals `ofReal (D x y)`.
* `exists_radius_internalMetric_eq`: the same, uniformly over a Euclidean closed ball around a point of `O`.
* `eventually_eqOn_of_internal`: from an internal-metric identity for a nonnegative field `m`, the plain identity
  `m = b · D` on `closedBall z (7 s) ×ˢ closedBall z (7 s)` for all small `s`. This is the form of `hDp` needed by
  `ae_fitting_of_decoders` (`FirstPass/S11i/Step8Fitting.lean`), with the eventual-in-`s` quantifier.

No inputs beyond `IsEuclideanLengthMetric` and nonnegativity of `D`.
-/

namespace HarmonicBalls.FirstPassS11iStep8Locality

open Set Metric Filter Topology
open scoped ENNReal

/-- **Gap lemma (locality of the internal metric).** Let `D` be a Euclidean length metric and `O ⊆ ℂ`. If every point
outside `O` is at `D`-distance at least `r` from `x` and from `y`, and `D x y < 2 r`, then the internal metric of `O`
between `x` and `y` is `ofReal (D x y)`. Proof: the lower bound is monotonicity of the internal metric; for the upper
bound, a nearly shortest ambient path from `x` to `y` has length `< 2 r`, so it cannot leave `O` (the two-segment bound
`ofReal_two_segment_le_pathLength` at an exit time would give length `≥ 2 r`). -/
theorem internalMetric_eq_ofReal_of_gap {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O : Set ℂ} {x y : ℂ} {r : ℝ}
    (hx : ∀ p, p ∉ O → r ≤ D x p) (hy : ∀ p, p ∉ O → r ≤ D y p) (hxy : D x y < 2 * r) :
    internalMetric D O x y = ENNReal.ofReal (D x y) := by
  have hD0 : 0 ≤ D x y := hnonneg x y
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨δ, hδ0, hδε, hδσ⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ (ε : ℝ) ∧ δ ≤ (2 * r - D x y) / 2 :=
      ⟨min (ε : ℝ) ((2 * r - D x y) / 2), lt_min (NNReal.coe_pos.2 hε) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    have hlt : internalMetric D univ x y < ENNReal.ofReal (D x y) + ENNReal.ofReal δ := by
      rw [← hD.ofReal_eq_internalMetric x y]
      exact ENNReal.lt_add_right ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.2 hδ0).ne'
    obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
    obtain ⟨-, hPlt⟩ := iInf_lt_iff.1 hP
    have hPO : ∀ t, P t ∈ O := by
      intro t
      by_contra hout
      have hsplit := hD.ofReal_two_segment_le_pathLength hnonneg P (t := (t : ℝ)) t.2
      have hext : P.extend (t : ℝ) = P t := Path.extend_extends' P t
      rw [hext] at hsplit
      have hsum : 2 * r ≤ D x (P t) + D (P t) y := by
        rw [hD.symm (P t) y]
        linarith [hx (P t) hout, hy (P t) hout]
      have h1 : ENNReal.ofReal (2 * r) ≤ pathLength D P :=
        (ENNReal.ofReal_le_ofReal hsum).trans hsplit
      have h2 : ENNReal.ofReal (D x y) + ENNReal.ofReal δ ≤ ENNReal.ofReal (2 * r) := by
        rw [← ENNReal.ofReal_add hD0 hδ0.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      exact lt_irrefl _ ((h1.trans_lt hPlt).trans_le h2)
    have hle : internalMetric D O x y ≤ pathLength D P := by
      unfold internalMetric
      exact iInf₂_le P hPO
    have hδε' : ENNReal.ofReal δ ≤ (ε : ℝ≥0∞) :=
      (ENNReal.ofReal_le_ofReal hδε).trans_eq ENNReal.ofReal_coe_nnreal
    exact hle.trans (hPlt.le.trans (add_le_add le_rfl hδε'))
  · rw [hD.ofReal_eq_internalMetric x y]
    exact internalMetric_anti D (subset_univ O) x y

/-- **Uniform locality around a point of an open set.** Let `O` be Euclidean-open and `z ∈ O`. For all small `s > 0`,
the Euclidean closed ball `closedBall z (7 s)` lies in `O`, and the internal metric of `O` agrees with `ofReal D` on
pairs in that ball. The radius comes from `IsEuclideanLengthMetric.isOpen_iff` (the `D`-ball of radius `δ` about `z`
lies in `O`) and continuity of `D z ·` at `z`. -/
theorem exists_radius_internalMetric_eq {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O : Set ℂ} (hO : IsOpen O) {z : ℂ} (hz : z ∈ O) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      closedBall z (7 * s) ⊆ O ∧
      ∀ x ∈ closedBall z (7 * s), ∀ y ∈ closedBall z (7 * s),
        internalMetric D O x y = ENNReal.ofReal (D x y) := by
  obtain ⟨δ, hδ, hball⟩ := (hD.isOpen_iff O).1 hO z hz
  have hcont : Continuous (fun w => D z w) := by
    simpa only [hD.symm z] using hD.continuous_left z
  have hev : ∀ᶠ w in 𝓝 z, D z w < δ / 4 :=
    (hcont.tendsto z).eventually (gt_mem_nhds (by rw [hD.self_eq_zero]; positivity))
  obtain ⟨η, hη, hηball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨η / 8, by positivity, fun s hs hsη => ?_⟩
  have hnear : ∀ x ∈ closedBall z (7 * s), D z x < δ / 4 := fun x hx =>
    hηball (lt_of_le_of_lt (Metric.mem_closedBall.1 hx) (by linarith))
  have hsub : closedBall z (7 * s) ⊆ O := fun x hx =>
    hball x (lt_of_lt_of_le (hnear x hx) (by linarith))
  refine ⟨hsub, fun x hx y hy => ?_⟩
  have hout : ∀ p, p ∉ O → δ ≤ D z p := fun p hp => not_lt.1 fun h => hp (hball p h)
  have hxz := hnear x hx
  have hyz := hnear y hy
  refine internalMetric_eq_ofReal_of_gap hD hnonneg (r := 3 * δ / 4) (fun p hp => ?_) (fun p hp => ?_) ?_
  · linarith [hD.triangle z x p, hout p hp, hD.symm x z]
  · linarith [hD.triangle z y p, hout p hp, hD.symm y z]
  · linarith [hD.triangle x z y, hD.symm x z]

/-- **Eventual plain identity for a decoded metric.** Let `O` be Euclidean-open, `z ∈ O`, and let `m` be a nonnegative
field with `ofReal (m x y) = ofReal b · internalMetric D O x y` on `O × O` (the metric clause of
`LocalMetricReplacementStmt`, for a nonnegative normalisation of the decoder). Then for all small `s > 0`, the plain
identity `m x y = b · D x y` holds on `closedBall z (7 s) ×ˢ closedBall z (7 s)`. -/
theorem eventually_eqOn_of_internal {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {O : Set ℂ} (hO : IsOpen O) {z : ℂ} (hz : z ∈ O)
    {m : ℂ → ℂ → ℝ} {b : ℝ} (hb : 0 < b) (hm0 : ∀ x y, 0 ≤ m x y)
    (hm : ∀ x ∈ O, ∀ y ∈ O, ENNReal.ofReal (m x y) = ENNReal.ofReal b * internalMetric D O x y) :
    ∃ s0 : ℝ, 0 < s0 ∧ ∀ s : ℝ, 0 < s → s ≤ s0 →
      Set.EqOn (Function.uncurry m) (Function.uncurry fun x y => b * D x y)
        (closedBall z (7 * s) ×ˢ closedBall z (7 * s)) := by
  obtain ⟨s0, hs0, hloc⟩ := exists_radius_internalMetric_eq hD hnonneg hO hz
  refine ⟨s0, hs0, fun s hs hss => ?_⟩
  rintro ⟨x, y⟩ ⟨hx, hy⟩
  obtain ⟨hsub, hint⟩ := hloc s hs hss
  show m x y = b * D x y
  have h1 : ENNReal.ofReal (m x y) = ENNReal.ofReal (b * D x y) := by
    rw [hm x (hsub hx) y (hsub hy), hint x hx y hy, ENNReal.ofReal_mul hb.le]
  exact (ENNReal.ofReal_eq_ofReal_iff (hm0 x y) (mul_nonneg hb.le (hnonneg x y))).1 h1

end HarmonicBalls.FirstPassS11iStep8Locality

#print axioms HarmonicBalls.FirstPassS11iStep8Locality.internalMetric_eq_ofReal_of_gap
#print axioms HarmonicBalls.FirstPassS11iStep8Locality.exists_radius_internalMetric_eq
#print axioms HarmonicBalls.FirstPassS11iStep8Locality.eventually_eqOn_of_internal
