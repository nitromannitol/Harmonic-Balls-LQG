import HarmonicBalls.FirstPass.S11m.LocalRule
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11k.ExitLocality
import HarmonicBalls.Steps.Sec11.LocalPathLength

/-!
# Internal form of the local certificate rule (fp-S11m, owner z4)

The local events of `FirstPass/S11h/LocalEvents.lean` use ambient set distances `setDist D`. A decoder can only recover
internal metrics of open sets inside `B₇(0)` (route `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md`, sections 2.1-2.2
and 4). For a length metric `D`, each ambient set distance of the local events is an internal infimum on an explicit open
set (the cutting argument of route section 2.1; `ofReal_setDist_boundary_eq_internalMetric` and the exit lemmas of
`FirstPass/S11k/ExitLocality.lean`). This file restates the local rule with internal infima only and proves that it is
equivalent to the ambient rule for every length metric satisfying the buffered pinch geometry.

Domains: `L` uses `B₆(0)`, which contains `closure Q` (`closure_Q_subset` lies in `annulus 0 4 5`); `a₀`, `a₁`, `a₂` use
`B_{4δ}(0)`, which contains the closures of `B_{δ}`, `B_{2δ}` and `B_{3δ}`.
-/

namespace HarmonicBalls.S11m.IntRule

open HarmonicBalls.S11m.LocalRule
open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- The closure of `Q` lies in `B₆(0)` (buffered pinch geometry, `closure_Q_subset`). -/
theorem closure_Q_subset_ball_six {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) : closure Q ⊆ ball (0 : ℂ) 6 := by
  intro z hz
  have h5 : annulus (0 : ℂ) 4 5 ⊆ ball (0 : ℂ) 6 := fun w hw => ball_subset_ball (by norm_num : (5 : ℝ) ≤ 6) hw.1
  exact h5 (hgeo.closure_Q_subset hz).1

/-- The frontier of `Q` is nonempty: `Q` is nonempty, open and bounded, and `ℂ` is connected. -/
theorem frontier_Q_nonempty {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) : (frontier Q).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  rcases isClopen_iff.mp (isClopen_iff_frontier_eq_empty.mpr h) with h1 | h1
  · exact hgeo.isConnected_Q.nonempty.ne_empty h1
  · have h6 : (6 : ℂ) ∈ closure Q := by
      rw [h1, closure_univ]
      exact mem_univ _
    have h6' := closure_Q_subset_ball_six hgeo h6
    rw [mem_ball, dist_zero_right] at h6'
    norm_num at h6'

/-- A closed ball of radius `r` about `0` lies in the open ball of radius `R` when `0 < r < R`. -/
theorem closure_ball_zero_subset_of_lt {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    closure (ball (0 : ℂ) r) ⊆ ball (0 : ℂ) R := by
  rw [closure_ball _ hr.ne']
  exact closedBall_subset_ball hrR

/-- Ambient-to-internal form of the exit distance `L = D(closure Q', ∂Q)` (route section 2.1, first row). -/
theorem ofReal_pinchLocalL_eq_internal {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ENNReal.ofReal (pinchLocalL D Q' Q) =
      ⨅ x ∈ closure Q', ⨅ y ∈ frontier Q, internalMetric D (ball (0 : ℂ) 6) x y := by
  unfold pinchLocalL
  exact ofReal_setDist_boundary_eq_internalMetric hD hgeo.isOpen_Q hgeo.closure_Q'_subset_Q
    (closure_Q_subset_ball_six hgeo) hgeo.isConnected_Q'.nonempty.closure (frontier_Q_nonempty hgeo)

/-- Ambient-to-internal form of the exit distance `D(0, ∂B_δ)`. -/
theorem ofReal_setDist_origin_eq_internal {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ}
    (hδ : 0 < δ) :
    ENNReal.ofReal (setDist D {0} (sphere (0 : ℂ) δ)) =
      ⨅ y ∈ sphere (0 : ℂ) δ, internalMetric D (ball (0 : ℂ) (4 * δ)) 0 y :=
  ofReal_setDist_origin_sphere_eq_internalMetric hD hδ
    (closure_ball_zero_subset_of_lt hδ (by linarith))

/-- Ambient-to-internal form of the crossing distance `D(∂B_δ, ∂B_{2δ})`. -/
theorem ofReal_setDist_sphere_eq_internal {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ}
    (hδ : 0 < δ) :
    ENNReal.ofReal (setDist D (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ))) =
      ⨅ x ∈ sphere (0 : ℂ) δ, ⨅ y ∈ sphere (0 : ℂ) (2 * δ), internalMetric D (ball (0 : ℂ) (4 * δ)) x y :=
  ofReal_setDist_sphere_sphere_eq_internalMetric hD hδ
    (closure_ball_zero_subset_of_lt (by linarith) (by linarith))

/-- Ambient-to-internal form of the crossing distance `D(∂B_{2δ}, ∂B_{3δ})`. -/
theorem ofReal_setDist_outer_eq_internal {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ}
    (hδ : 0 < δ) :
    ENNReal.ofReal (setDist D (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ))) =
      ⨅ x ∈ sphere (0 : ℂ) (2 * δ), ⨅ y ∈ sphere (0 : ℂ) (3 * δ),
        internalMetric D (ball (0 : ℂ) (4 * δ)) x y := by
  have h3 : 0 < 3 * δ := by positivity
  have hfront : frontier (ball (0 : ℂ) (3 * δ)) = sphere (0 : ℂ) (3 * δ) := frontier_ball 0 h3.ne'
  have hsub : sphere (0 : ℂ) (2 * δ) ⊆ ball (0 : ℂ) (3 * δ) := by
    intro x hx
    rw [mem_sphere_zero_iff_norm] at hx
    rw [mem_ball_zero_iff]
    linarith
  have hne2 : (sphere (0 : ℂ) (2 * δ)).Nonempty :=
    ⟨((2 * δ : ℝ) : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]⟩
  have hne3 : (frontier (ball (0 : ℂ) (3 * δ))).Nonempty := by
    rw [hfront]
    exact ⟨((3 * δ : ℝ) : ℂ), by rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity)]⟩
  have h : ENNReal.ofReal (setDist D (sphere (0 : ℂ) (2 * δ)) (frontier (ball (0 : ℂ) (3 * δ)))) =
      ⨅ x ∈ sphere (0 : ℂ) (2 * δ), ⨅ y ∈ frontier (ball (0 : ℂ) (3 * δ)),
        internalMetric D (ball (0 : ℂ) (4 * δ)) x y :=
    ofReal_setDist_boundary_eq_internalMetric hD isOpen_ball hsub
      (closure_ball_zero_subset_of_lt h3 (by linarith)) hne2 hne3
  rw [hfront] at h
  exact h

/-- Internal form of the local first event `E₁` (note eq. (3.1)): the exit distance `L` and the origin distance
`a₀` are internal infima; the diameter term is unchanged. -/
def pinchFirstEventInt (D : ℂ → ℂ → ℝ) (W T Q' Q : Set ℂ) (δ : ℝ) : Prop :=
  pinchLocalA D W Q δ < (⨅ x ∈ closure Q', ⨅ y ∈ frontier Q, internalMetric D (ball (0 : ℂ) 6) x y) ∧
    internalDiam D δ (closure (T \ thickening (3 * δ) W)) <
      ⨅ y ∈ sphere (0 : ℂ) δ, internalMetric D (ball (0 : ℂ) (4 * δ)) 0 y

/-- Internal form of the local second event `E₂(M)`: the crossing distance `a₁` is an internal infimum. -/
def pinchSecondEventInt (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (U V : Set ℂ) (δ M : ℝ) : Prop :=
  internalDiam D δ (closure V) <
      (⨅ x ∈ sphere (0 : ℂ) δ, ⨅ y ∈ sphere (0 : ℂ) (2 * δ), internalMetric D (ball (0 : ℂ) (4 * δ)) x y) ∧
    ENNReal.ofReal M * annulusGreenPotentialSup μ 0 3 6 < μ U

/-- Internal form of the local third event `E₃`: the crossing distance `a₂` is an internal infimum. -/
def pinchThirdEventInt (D : ℂ → ℂ → ℝ) (V W : Set ℂ) (δ : ℝ) : Prop :=
  internalDiam D δ (closure (thickening (3 * δ) W \ V)) <
    (⨅ x ∈ sphere (0 : ℂ) (2 * δ), ⨅ y ∈ sphere (0 : ℂ) (3 * δ),
      internalMetric D (ball (0 : ℂ) (4 * δ)) x y)

/-- The internal form of the local certificate rule (`pinchLocalRule` with internal set distances). -/
def pinchLocalRuleInt (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (W T Q' Q U V : Set ℂ) (δ M : ℝ) : Prop :=
  pinchFirstEventInt D W T Q' Q δ ∧ pinchSecondEventInt μ D U V δ M ∧ pinchThirdEventInt D V W δ

theorem pinchFirstEventLocal_iff_int {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    pinchFirstEventLocal D W T Q' Q δ ↔ pinchFirstEventInt D W T Q' Q δ := by
  unfold pinchFirstEventLocal pinchFirstEventInt
  rw [ofReal_pinchLocalL_eq_internal hD hgeo, ofReal_setDist_origin_eq_internal hD hgeo.delta_pos]

theorem pinchSecondEventLocal_iff_int {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (μ : Measure ℂ)
    {δ M : ℝ} (hδ : 0 < δ) (U V : Set ℂ) :
    pinchSecondEventLocal μ D U V δ M ↔ pinchSecondEventInt μ D U V δ M := by
  unfold pinchSecondEventLocal pinchSecondEventInt
  rw [ofReal_setDist_sphere_eq_internal hD hδ]

theorem pinchThirdEventLocal_iff_int {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {δ : ℝ} (hδ : 0 < δ)
    (V W : Set ℂ) :
    pinchThirdEventLocal D V W δ ↔ pinchThirdEventInt D V W δ := by
  unfold pinchThirdEventLocal pinchThirdEventInt
  rw [ofReal_setDist_outer_eq_internal hD hδ]

/-- The local certificate rule and its internal form agree for every length metric in the buffered pinch geometry. -/
theorem pinchLocalRule_iff_int {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (μ : Measure ℂ) (M : ℝ) :
    pinchLocalRule μ D W T Q' Q U V δ M ↔ pinchLocalRuleInt μ D W T Q' Q U V δ M := by
  unfold pinchLocalRule pinchLocalRuleInt
  rw [pinchFirstEventLocal_iff_int hD hgeo, pinchSecondEventLocal_iff_int hD μ hgeo.delta_pos U V,
    pinchThirdEventLocal_iff_int hD hgeo.delta_pos V W]

/-- A nonzero finite scalar passes through a double infimum over two index sets. -/
theorem biInf_const_mul_eq {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ⊤) (S T : Set ℂ) (f : ℂ → ℂ → ℝ≥0∞) :
    (⨅ x ∈ S, ⨅ y ∈ T, c * f x y) = c * ⨅ x ∈ S, ⨅ y ∈ T, f x y := by
  simp only [ENNReal.mul_iInf_of_ne hc0 hcT]

/-- A nonzero finite scalar passes through a single infimum over an index set. -/
theorem uniInf_const_mul_eq {c : ℝ≥0∞} (hc0 : c ≠ 0) (hcT : c ≠ ⊤) (S : Set ℂ) (f : ℂ → ℝ≥0∞) :
    (⨅ y ∈ S, c * f y) = c * ⨅ y ∈ S, f y := by
  simp only [ENNReal.mul_iInf_of_ne hc0 hcT]

/-- The first internal local event is invariant under `D ↦ c D`, `c > 0`. -/
theorem pinchFirstEventInt_const_mul_iff (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (W T Q' Q : Set ℂ) (δ : ℝ) :
    pinchFirstEventInt (fun x y => c * D x y) W T Q' Q δ ↔ pinchFirstEventInt D W T Q' Q δ := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold pinchFirstEventInt
  simp only [pinchLocalA_const_mul D hc, internalMetric_const_mul D hc, internalDiam_const_mul D hc,
    uniInf_const_mul_eq hc0 hcTop, ennreal_mul_lt_mul_iff_of_ne hc0 hcTop]

/-- The third internal local event is invariant under `D ↦ c D`, `c > 0`. -/
theorem pinchThirdEventInt_const_mul_iff (D : ℂ → ℂ → ℝ) {c : ℝ} (hc : 0 < c) (V W : Set ℂ) (δ : ℝ) :
    pinchThirdEventInt (fun x y => c * D x y) V W δ ↔ pinchThirdEventInt D V W δ := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold pinchThirdEventInt
  simp only [internalDiam_const_mul D hc, internalMetric_const_mul D hc, biInf_const_mul_eq hc0 hcTop,
    ennreal_mul_lt_mul_iff_of_ne hc0 hcTop]

/-- The second internal local event is invariant under `μ ↦ a μ` and `D ↦ c D`, `a, c > 0`. -/
theorem pinchSecondEventInt_smul_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (U V : Set ℂ) (δ M : ℝ) :
    pinchSecondEventInt (ENNReal.ofReal a • μ) (fun x y => c * D x y) U V δ M ↔
      pinchSecondEventInt μ D U V δ M := by
  have hc0 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  have hcTop : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  have ha0 : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  have haTop : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hP : ENNReal.ofReal M * (ENNReal.ofReal a * annulusGreenPotentialSup μ 0 3 6) < ENNReal.ofReal a * μ U ↔
      ENNReal.ofReal M * annulusGreenPotentialSup μ 0 3 6 < μ U := by
    rw [← mul_assoc, mul_comm (ENNReal.ofReal M), mul_assoc, ennreal_mul_lt_mul_iff_of_ne ha0 haTop]
  unfold pinchSecondEventInt
  simp only [internalDiam_const_mul D hc, internalMetric_const_mul D hc, biInf_const_mul_eq hc0 hcTop,
    ennreal_mul_lt_mul_iff_of_ne hc0 hcTop, HarmonicBalls.S11n.annulusGreenPotentialSup_smul,
    Measure.smul_apply, smul_eq_mul]
  exact and_congr_right (fun _ => hP)

/-- The internal local certificate rule is invariant under `μ ↦ a μ` and `D ↦ c D`, `a, c > 0` (equation (3)). -/
theorem pinchLocalRuleInt_smul_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (W T Q' Q U V : Set ℂ) (δ M : ℝ) :
    pinchLocalRuleInt (ENNReal.ofReal a • μ) (fun x y => c * D x y) W T Q' Q U V δ M ↔
      pinchLocalRuleInt μ D W T Q' Q U V δ M := by
  unfold pinchLocalRuleInt
  rw [pinchFirstEventInt_const_mul_iff D hc, pinchSecondEventInt_smul_iff μ D ha hc,
    pinchThirdEventInt_const_mul_iff D hc]

end HarmonicBalls.S11m.IntRule
