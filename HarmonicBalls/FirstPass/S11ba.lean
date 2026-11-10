import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.LocalEvents

/-! # Admissibility of the decoded domains of the corrected Lemma 11.12 (fp-S11ba, owner z6)

The decoded values of internal distances (`S11m.decodedVal_ae_family`, `FirstPass/S11m/DecodedLocal.lean:58`) are valid on
a domain `O` that is admissible: open, `O \ {0} ⊆ ball 0 7 \ {0}`, and connected whenever `0 ∈ O`
(`DecodedAdmissible`). This file proves admissibility for every domain on which the internal forms of the local
certificate rule evaluate an internal metric or internal diameter:

* `pinchOmegaGeom W Q δ`: the component of `0` in `B₇ \ (closure (B_{2δ} Q) ∪ closure (B_{2δ} W))`. It is the domain of
  `pinchLocalA` (`FirstPass/S11h/LocalEvents.lean:30`, `:26` for the definition), used by `pinchFirstEventInt`
  (`FirstPass/S11m/IntRule.lean:107`) on `∂B₅`.
* `ball 0 6`: domain of `internalMetric D (ball 0 6) x y` in `pinchFirstEventInt` (`IntRule.lean:107`).
* `ball 0 (4δ)`: domain of `internalMetric D (ball 0 (4δ)) …` in `pinchFirstEventInt` (`IntRule.lean:108`),
  `pinchSecondEventInt` (`IntRule.lean:114`) and `pinchThirdEventInt` (`IntRule.lean:121`).
* `thickening δ (closure (T \ thickening (3δ) W))`: the δ-neighbourhood in `internalDiam D δ (closure (T \ thickening (3δ) W))`
  (`Draft/Section11.lean:89`, `internalDiam` uses `internalMetric D (thickening δ A)`), in `pinchFirstEventInt` (`IntRule.lean:108`).
* `thickening δ (closure V)`: `internalDiam D δ (closure V)` in `pinchSecondEventInt` (`IntRule.lean:113`).
* `thickening δ (closure (thickening (3δ) W \ V))`: `internalDiam D δ (closure (thickening (3δ) W \ V))` in
  `pinchThirdEventInt` (`IntRule.lean:119`).

Each admissibility is proved from the buffer and annulus clauses of `IsBufferedPinchGeometry`
(`FirstPass/S11h/Faithful.lean:36`: `closure_T_subset`, `V_subset`, `W_subset`, `delta_pos`, `delta_lt`). The origin lies
outside every thickened diameter set, since those sets lie in `{1 - 3δ ≤ ‖z‖}` and `δ < 1/1000`, so the connectivity
clause is vacuous for them. `pinchOmegaGeom` is connected because it is a connected component of an open set. No
statement here uses the hypothesis `hR1`; it is part of the stated form only.
-/

namespace HarmonicBalls.S11ba

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- A domain `O` is admissible for the decoding of internal distances: open, its punctured part lies in the punctured
ball `ball 0 7 \ {0}`, and it is connected whenever it contains the origin (the hypotheses of
`S11m.decodedVal_ae_family`, `FirstPass/S11m/DecodedLocal.lean:58`). -/
def DecodedAdmissible (O : Set ℂ) : Prop :=
  IsOpen O ∧ O \ {0} ⊆ ball (0 : ℂ) 7 \ {0} ∧ ((0 : ℂ) ∈ O → IsConnected O)

/-- An open ball centred at the origin of radius at most `7` is admissible (it is convex). -/
theorem decodedAdmissible_ball {ρ : ℝ} (hρ : ρ ≤ 7) : DecodedAdmissible (ball (0 : ℂ) ρ) := by
  refine ⟨isOpen_ball, fun z hz => ⟨ball_subset_ball hρ hz.1, hz.2⟩, fun h0 => ?_⟩
  exact (convex_ball (0 : ℂ) ρ).isConnected ⟨0, h0⟩

/-- A connected component of an open subset of `B₇` is admissible. -/
theorem decodedAdmissible_connectedComponentIn {F : Set ℂ} (hF : IsOpen F) (hFb : F ⊆ ball (0 : ℂ) 7) (x : ℂ) :
    DecodedAdmissible (connectedComponentIn F x) := by
  refine ⟨hF.connectedComponentIn, fun z hz => ⟨hFb (connectedComponentIn_subset F x hz.1), hz.2⟩, fun h0 => ?_⟩
  exact isConnected_connectedComponentIn_iff.2 (connectedComponentIn_nonempty_iff.1 ⟨0, h0⟩)

/-- Norm bounds on a closure from bounds on the set. -/
lemma norm_le_of_closure {S : Set ℂ} {R : ℝ} (hS : ∀ s ∈ S, ‖s‖ ≤ R) : ∀ k ∈ closure S, ‖k‖ ≤ R :=
  fun _ hk => closure_minimal (fun s hs => hS s hs) (isClosed_le continuous_norm continuous_const) hk

/-- Lower norm bounds on a closure from bounds on the set. -/
lemma le_norm_of_closure {S : Set ℂ} {r : ℝ} (hS : ∀ s ∈ S, r ≤ ‖s‖) : ∀ k ∈ closure S, r ≤ ‖k‖ :=
  fun _ hk => closure_minimal (fun s hs => hS s hs) (isClosed_le continuous_const continuous_norm) hk

/-- The two-sided norm bounds of the open annulus `annulus 0 r₁ r₂ = ball 0 r₂ \ closedBall 0 r₁`. -/
lemma norm_bounds_of_annulus {z : ℂ} {r₁ r₂ : ℝ} (hz : z ∈ annulus (0 : ℂ) r₁ r₂) :
    r₁ < ‖z‖ ∧ ‖z‖ < r₂ := by
  obtain ⟨h1, h2⟩ := hz
  constructor
  · have h := h2
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at h
    exact h
  · have h := h1
    rw [Metric.mem_ball, dist_zero_right] at h
    exact h

/-- Points of the `ε`-neighbourhood of a set in `B_R` lie in `B_{R+ε}`. -/
lemma norm_lt_of_mem_thickening {S : Set ℂ} {ε R : ℝ} (hS : ∀ s ∈ S, ‖s‖ < R) {z : ℂ}
    (hz : z ∈ thickening ε S) : ‖z‖ < R + ε := by
  obtain ⟨s, hs, hzs⟩ := mem_thickening_iff.1 hz
  rw [dist_eq_norm] at hzs
  have := norm_sub_norm_le z s
  linarith [hS s hs]

/-- Points of the `ε`-neighbourhood of a set in `{r < ‖·‖}` lie in `{r - ε < ‖·‖}`. -/
lemma lt_norm_of_mem_thickening {S : Set ℂ} {ε r : ℝ} (hS : ∀ s ∈ S, r < ‖s‖) {z : ℂ}
    (hz : z ∈ thickening ε S) : r - ε < ‖z‖ := by
  obtain ⟨s, hs, hzs⟩ := mem_thickening_iff.1 hz
  rw [dist_comm, dist_eq_norm] at hzs
  have := norm_sub_norm_le s z
  linarith [hS s hs]

/-- **Admissibility of a thickening.** If every point of `K` has norm at most `R` and at least `r ≥ δ`, and `R + δ ≤ 7`,
then the `δ`-neighbourhood of `K` is admissible: the origin is not in it, since `dist 0 k < δ ≤ r ≤ ‖k‖` is impossible. -/
theorem decodedAdmissible_thickening {K : Set ℂ} {δ R r : ℝ} (hδr : δ ≤ r) (hR : R + δ ≤ 7)
    (hK : ∀ k ∈ K, ‖k‖ ≤ R) (hr : ∀ k ∈ K, r ≤ ‖k‖) : DecodedAdmissible (thickening δ K) := by
  refine ⟨isOpen_thickening, fun z hz => ⟨?_, hz.2⟩, fun h0 => ?_⟩
  · obtain ⟨k, hk, hzk⟩ := mem_thickening_iff.1 hz.1
    rw [dist_eq_norm] at hzk
    have := norm_sub_norm_le z k
    rw [mem_ball_zero_iff]
    linarith [hK k hk]
  · exfalso
    obtain ⟨k, hk, hzk⟩ := mem_thickening_iff.1 h0
    rw [dist_zero_left] at hzk
    linarith [hr k hk]

/-- **Pinch geometry: the origin component.** The component `Ω` of `0` in `B₇ \ (closure (B_{2δ} Q) ∪ closure (B_{2δ} W))`
(`FirstPass/S11h/LocalEvents.lean:26`) is admissible; it is the domain of `pinchLocalA`. -/
theorem admissible_pinchOmegaGeom {U V W T Q' Q : Set ℂ} {δ : ℝ} (_hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (_hR1 : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) : DecodedAdmissible (pinchOmegaGeom W Q δ) := by
  unfold pinchOmegaGeom
  exact decodedAdmissible_connectedComponentIn (isOpen_ball.sdiff (isClosed_closure.union isClosed_closure))
    sdiff_subset 0

/-- **Ball `B₆`** (domain of the internal metric in `pinchFirstEventInt`, `IntRule.lean:107`). -/
theorem admissible_ball_six {U V W T Q' Q : Set ℂ} {δ : ℝ} (_hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (_hR1 : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) : DecodedAdmissible (ball (0 : ℂ) 6) :=
  decodedAdmissible_ball (by norm_num)

/-- **Ball `B_{4δ}`** (domain of the internal metric in `pinchFirstEventInt`, `pinchSecondEventInt`, `pinchThirdEventInt`). -/
theorem admissible_ball_four_delta {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (_hR1 : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) : DecodedAdmissible (ball (0 : ℂ) (4 * δ)) :=
  decodedAdmissible_ball (by linarith [hG.delta_lt])

/-- **δ-neighbourhood of `closure (T \ B_{3δ}(W))`**, the domain of `internalDiam` in `pinchFirstEventInt`
(`IntRule.lean:108`). Its closure lies in `{1 ≤ ‖·‖ ≤ 6}` (`closure_T_subset`). -/
theorem admissible_diam_first {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (_hR1 : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) :
    DecodedAdmissible (thickening δ (closure (T \ thickening (3 * δ) W))) := by
  have hb : ∀ s ∈ T \ thickening (3 * δ) W, 1 ≤ ‖s‖ ∧ ‖s‖ ≤ 6 := fun s hs =>
    ⟨((norm_bounds_of_annulus (hG.closure_T_subset (subset_closure hs.1))).1).le,
     ((norm_bounds_of_annulus (hG.closure_T_subset (subset_closure hs.1))).2).le⟩
  exact decodedAdmissible_thickening (by linarith [hG.delta_lt, hG.delta_pos]) (by linarith [hG.delta_lt])
    (norm_le_of_closure fun s hs => (hb s hs).2) (le_norm_of_closure fun s hs => (hb s hs).1)

/-- **δ-neighbourhood of `closure V`**, the domain of `internalDiam` in `pinchSecondEventInt` (`IntRule.lean:113`).
`V ⊆ annulus 0 1 2`. -/
theorem admissible_diam_second {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (_hR1 : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) :
    DecodedAdmissible (thickening δ (closure V)) := by
  have hb : ∀ s ∈ V, 1 ≤ ‖s‖ ∧ ‖s‖ ≤ 2 := fun s hs =>
    ⟨((norm_bounds_of_annulus (hG.V_subset hs)).1).le, ((norm_bounds_of_annulus (hG.V_subset hs)).2).le⟩
  exact decodedAdmissible_thickening (by linarith [hG.delta_lt, hG.delta_pos]) (by linarith [hG.delta_lt])
    (norm_le_of_closure fun s hs => (hb s hs).2) (le_norm_of_closure fun s hs => (hb s hs).1)

/-- **δ-neighbourhood of `closure (B_{3δ}(W) \ V)`**, the domain of `internalDiam` in `pinchThirdEventInt`
(`IntRule.lean:119`). Points of `B_{3δ}(W)` have norm in `(1 - 3δ, 2 + 3δ)`, since `W ⊆ annulus 0 1 2`. -/
theorem admissible_diam_third {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (_hR1 : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) :
    DecodedAdmissible (thickening δ (closure (thickening (3 * δ) W \ V))) := by
  have hW : ∀ w ∈ W, 1 < ‖w‖ ∧ ‖w‖ < 2 := fun w hw => norm_bounds_of_annulus (hG.W_subset hw)
  have hup : ∀ s ∈ thickening (3 * δ) W \ V, ‖s‖ ≤ 2 + 3 * δ := fun s hs =>
    (norm_lt_of_mem_thickening (fun w hw => (hW w hw).2) hs.1).le
  have hlo : ∀ s ∈ thickening (3 * δ) W \ V, 1 - 3 * δ ≤ ‖s‖ := fun s hs =>
    (lt_norm_of_mem_thickening (fun w hw => (hW w hw).1) hs.1).le
  exact decodedAdmissible_thickening (by linarith [hG.delta_lt, hG.delta_pos]) (by linarith [hG.delta_lt])
    (norm_le_of_closure hup) (le_norm_of_closure hlo)

/-- **Bundled admissibility of the decoded domains of the local rule** (fp-S11ba). Every domain on which the internal forms
`pinchFirstEventInt`, `pinchSecondEventInt`, `pinchThirdEventInt` (`FirstPass/S11m/IntRule.lean:106-122`) and the
local value `pinchLocalA` (`FirstPass/S11h/LocalEvents.lean:30`) evaluate an internal metric or internal diameter. -/
theorem pinchDomains_admissible {U V W T Q' Q : Set ℂ} {δ : ℝ} (hG : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hR1 : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ) :
    DecodedAdmissible (pinchOmegaGeom W Q δ) ∧ DecodedAdmissible (ball (0 : ℂ) 6) ∧
      DecodedAdmissible (ball (0 : ℂ) (4 * δ)) ∧
      DecodedAdmissible (thickening δ (closure (T \ thickening (3 * δ) W))) ∧
      DecodedAdmissible (thickening δ (closure V)) ∧
      DecodedAdmissible (thickening δ (closure (thickening (3 * δ) W \ V))) :=
  ⟨admissible_pinchOmegaGeom hG hR1, admissible_ball_six hG hR1, admissible_ball_four_delta hG hR1,
    admissible_diam_first hG hR1, admissible_diam_second hG hR1, admissible_diam_third hG hR1⟩

end HarmonicBalls.S11ba

#print axioms HarmonicBalls.S11ba.pinchDomains_admissible
