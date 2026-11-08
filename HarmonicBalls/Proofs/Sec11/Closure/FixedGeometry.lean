import HarmonicBalls.Defs.Geometry
import HarmonicBalls.Proofs.Sec6.HarnackIteration

/-!
# Fixed pinch-point configuration (Section 11, draft lines 271–311)

Written argument: `notes/sec11-proof/sec11-proof.tex`, paragraph "Fixed geometry" (its draft lines 271–311).
The explicit sets `U = B_{.01}(1.5)`, `Q' = B_{.04}(-4.4)`, `Q = B_{.1}(-4.4)` and
`T = B_{.1}(1.5) ∪ {x + iy : 1.5 < x < 4.9, |y| < .05} ∪ 𝔸_{4.8,5}` form an `IsPinchPointConfiguration`
(`HarmonicBalls/Defs/Geometry.lean`). This module proves that such a configuration exists, which is the
existential witness of `PinchEventPositiveProbabilityStmt` (`HarmonicBalls/Draft/Section11.lean:246`).
The buffered `IsCorrectedPinchConfiguration` used by the conditional chain is not constructed here.
-/

namespace HarmonicBalls

open Metric Set

/-- The point `1.5` of the complex plane, as the cast of a real number. -/
noncomputable def pinchCentreA : ℂ := ((3 / 2 : ℝ) : ℂ)

/-- The point `-4.4` of the complex plane, as the cast of a real number. -/
noncomputable def pinchCentreB : ℂ := ((-22 / 5 : ℝ) : ℂ)

/-- `U = B_{.01}(1.5)` (draft line 273). -/
def fixedU : Set ℂ := ball pinchCentreA (1 / 100)

/-- `Q' = B_{.04}(-4.4)` (draft line 273). -/
def fixedQ' : Set ℂ := ball pinchCentreB (1 / 25)

/-- `Q = B_{.1}(-4.4)` (draft line 273). -/
def fixedQ : Set ℂ := ball pinchCentreB (1 / 10)

/-- The strip `{x + iy : 1.5 < x < 4.9, |y| < .05}` in the definition of `T` (draft line 277). -/
def fixedStrip : Set ℂ :=
  ({z : ℂ | 3 / 2 < z.re} ∩ {z : ℂ | z.re < 49 / 10}) ∩
    ({z : ℂ | z.im < 1 / 20} ∩ {z : ℂ | -(1 / 20) < z.im})

/-- `T = B_{.1}(1.5) ∪ {1.5 < x < 4.9, |y| < .05} ∪ 𝔸_{4.8,5}` (draft line 277). -/
def fixedT : Set ℂ := ball pinchCentreA (1 / 10) ∪ fixedStrip ∪ annulus 0 (24 / 5) 5

lemma pinchCentreA_re : pinchCentreA.re = 3 / 2 := by simp [pinchCentreA]

lemma pinchCentreB_re : pinchCentreB.re = -22 / 5 := by simp [pinchCentreB]

lemma norm_pinchCentreA : ‖pinchCentreA‖ = 3 / 2 := by
  rw [pinchCentreA, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]

lemma norm_pinchCentreB : ‖pinchCentreB‖ = 22 / 5 := by
  rw [pinchCentreB, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by norm_num)]
  norm_num

lemma norm_ofReal_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ‖(x : ℂ)‖ = x := by
  rw [Complex.norm_real, Real.norm_of_nonneg hx]

/-- The real part of a difference is at most the norm of the difference. -/
lemma abs_re_sub_le (z w : ℂ) : |z.re - w.re| ≤ ‖z - w‖ := by
  simpa [Complex.sub_re, Real.norm_eq_abs] using RCLike.norm_re_le_norm (z - w)

lemma isLinear_re : IsLinearMap ℝ (fun z : ℂ => z.re) :=
  ⟨fun x y => Complex.add_re x y, fun c x => by simp⟩

lemma isLinear_im : IsLinearMap ℝ (fun z : ℂ => z.im) :=
  ⟨fun x y => Complex.add_im x y, fun c x => by simp⟩

lemma convex_fixedStrip : Convex ℝ fixedStrip :=
  ((convex_halfSpace_gt isLinear_re _).inter (convex_halfSpace_lt isLinear_re _)).inter
    ((convex_halfSpace_lt isLinear_im _).inter (convex_halfSpace_gt isLinear_im _))

lemma isOpen_fixedStrip : IsOpen fixedStrip :=
  ((isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)).inter
    ((isOpen_lt Complex.continuous_im continuous_const).inter
      (isOpen_lt continuous_const Complex.continuous_im))

lemma isOpen_fixedAnnulus (c : ℂ) (r₁ r₂ : ℝ) : IsOpen (annulus c r₁ r₂) := by
  unfold annulus
  exact isOpen_ball.sdiff isClosed_closedBall

lemma isOpen_fixedT : IsOpen fixedT :=
  (isOpen_ball.union isOpen_fixedStrip).union (isOpen_fixedAnnulus 0 _ _)

lemma fixedPinch_closure_U : closure fixedU ⊆ fixedT := by
  intro z hz
  unfold fixedU at hz
  have h1 : z ∈ closedBall pinchCentreA (1 / 100) := closure_ball_subset_closedBall hz
  have h2 : z ∈ ball pinchCentreA (1 / 10) := closedBall_subset_ball (by norm_num) h1
  exact Or.inl (Or.inl h2)

lemma fixedPinch_closure_Q' : closure fixedQ' ⊆ fixedQ := by
  intro z hz
  unfold fixedQ' at hz
  unfold fixedQ
  exact closedBall_subset_ball (by norm_num) (closure_ball_subset_closedBall hz)

lemma fixedU_subset_annulus : fixedU ⊆ annulus 0 1 2 := by
  intro z hz
  unfold fixedU at hz
  rw [mem_ball, dist_eq_norm] at hz
  have h := abs_le.1 (abs_norm_sub_norm_le z pinchCentreA)
  rw [norm_pinchCentreA] at h
  unfold annulus
  refine ⟨?_, ?_⟩
  · rw [mem_ball, dist_zero_right]
    linarith [h.1, h.2]
  · rw [mem_closedBall, dist_zero_right, not_le]
    linarith [h.1, h.2]

/-- The closed set `{7/5 ≤ Re z} ∪ {24/5 ≤ |z|}` contains `T`. -/
lemma fixedT_subset_F : fixedT ⊆ {z : ℂ | 7 / 5 ≤ z.re} ∪ {z : ℂ | 24 / 5 ≤ ‖z‖} := by
  rintro z ((hz | hz) | hz)
  · left
    have h := abs_re_sub_le z pinchCentreA
    rw [mem_ball, dist_eq_norm] at hz
    rw [pinchCentreA_re] at h
    have := neg_abs_le (z.re - 3 / 2)
    show 7 / 5 ≤ z.re
    linarith
  · left
    simp only [fixedStrip, mem_inter_iff, Set.mem_ofPred_eq] at hz
    show 7 / 5 ≤ z.re
    linarith [hz.1.1]
  · right
    unfold annulus at hz
    have hnb := hz.2
    rw [mem_closedBall, dist_zero_right, not_le] at hnb
    show 24 / 5 ≤ ‖z‖
    linarith

lemma fixedT_subset_annulus : fixedT ⊆ annulus 0 1 5 := by
  rintro z ((hz | hz) | hz)
  · rw [mem_ball, dist_eq_norm] at hz
    have h := abs_le.1 (abs_norm_sub_norm_le z pinchCentreA)
    rw [norm_pinchCentreA] at h
    unfold annulus
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      linarith [h.1, h.2]
    · rw [mem_closedBall, dist_zero_right, not_le]
      linarith [h.1, h.2]
  · simp only [fixedStrip, mem_inter_iff, Set.mem_ofPred_eq] at hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    have hre : |z.re| = z.re := abs_of_pos (by linarith)
    have hn1 : z.re ≤ ‖z‖ := Complex.re_le_norm z
    have hn2 := Complex.norm_le_abs_re_add_abs_im z
    have him : |z.im| < 1 / 20 := abs_lt.2 ⟨h4, h3⟩
    unfold annulus
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      linarith
    · rw [mem_closedBall, dist_zero_right, not_le]
      linarith
  · unfold annulus at hz
    obtain ⟨hb, hnb⟩ := hz
    rw [mem_ball, dist_zero_right] at hb
    rw [mem_closedBall, dist_zero_right, not_le] at hnb
    unfold annulus
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      linarith
    · rw [mem_closedBall, dist_zero_right, not_le]
      linarith

lemma isClosed_fixedF :
    IsClosed ({z : ℂ | 7 / 5 ≤ z.re} ∪ {z : ℂ | 24 / 5 ≤ ‖z‖}) :=
  (isClosed_le continuous_const Complex.continuous_re).union
    (isClosed_le continuous_const continuous_norm)

lemma fixedQ_subset : fixedQ ⊆ annulus 0 4 5 \ closure fixedT := by
  intro z hz
  unfold fixedQ at hz
  rw [mem_ball, dist_eq_norm] at hz
  have h := abs_le.1 (abs_norm_sub_norm_le z pinchCentreB)
  rw [norm_pinchCentreB] at h
  have hre := abs_le.1 (abs_re_sub_le z pinchCentreB)
  rw [pinchCentreB_re] at hre
  have hF : closure fixedT ⊆ {z : ℂ | 7 / 5 ≤ z.re} ∪ {z : ℂ | 24 / 5 ≤ ‖z‖} :=
    closure_minimal fixedT_subset_F isClosed_fixedF
  refine ⟨?_, ?_⟩
  · unfold annulus
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right]
      linarith [h.1, h.2]
    · rw [mem_closedBall, dist_zero_right, not_le]
      linarith [h.1, h.2]
  · intro hcl
    rcases hF hcl with h1 | h1
    · have h1' : 7 / 5 ≤ z.re := h1
      linarith [hre.2]
    · have h1' : 24 / 5 ≤ ‖z‖ := h1
      linarith [h.2]

lemma mem_fixedStrip_ofReal {x : ℝ} (h1 : 3 / 2 < x) (h2 : x < 49 / 10) :
    (x : ℂ) ∈ fixedStrip := by
  simp only [fixedStrip, mem_inter_iff, Set.mem_ofPred_eq, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨⟨h1, h2⟩, by norm_num, by norm_num⟩

lemma isConnected_fixedT : IsConnected fixedT := by
  have hz0 : ((31 / 20 : ℝ) : ℂ) ∈ ball pinchCentreA (1 / 10) := by
    rw [mem_ball, dist_eq_norm, pinchCentreA, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_lt]
    constructor <;> norm_num
  have hz0s : ((31 / 20 : ℝ) : ℂ) ∈ fixedStrip := mem_fixedStrip_ofReal (by norm_num) (by norm_num)
  have hz1s : ((97 / 20 : ℝ) : ℂ) ∈ fixedStrip := mem_fixedStrip_ofReal (by norm_num) (by norm_num)
  have hz1a : ((97 / 20 : ℝ) : ℂ) ∈ annulus 0 (24 / 5) 5 := by
    unfold annulus
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, norm_ofReal_of_nonneg (by norm_num)]
      norm_num
    · rw [mem_closedBall, dist_zero_right, norm_ofReal_of_nonneg (by norm_num), not_le]
      norm_num
  have h1 : IsPreconnected (ball pinchCentreA (1 / 10) ∪ fixedStrip) :=
    IsPreconnected.union _ hz0 hz0s (convex_ball _ _).isPreconnected convex_fixedStrip.isPreconnected
  have h2 : IsPreconnected fixedT :=
    IsPreconnected.union _ (Or.inr hz1s) hz1a h1 (Section6.isPreconnected_annulus 0 (by norm_num) 5)
  exact ⟨⟨pinchCentreA, Or.inl (Or.inl (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 10)))⟩, h2⟩

lemma sphere_subset_frontier_fixedT : sphere (0 : ℂ) 5 ⊆ frontier fixedT := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  unfold frontier
  refine ⟨?_, ?_⟩
  · refine closure_mono (fun w hw => Or.inr hw) ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    set t : ℝ := min (ε / 2) (1 / 10) with ht
    have htpos : 0 < t := lt_min (by linarith) (by norm_num)
    have htle1 : t ≤ ε / 2 := min_le_left _ _
    have htle2 : t ≤ 1 / 10 := min_le_right _ _
    have hnorm : ‖(1 - t / 5 : ℝ) • z‖ = 5 - t := by
      rw [norm_smul, hz, Real.norm_of_nonneg (by linarith)]
      ring
    have hdist : dist z ((1 - t / 5 : ℝ) • z) = t := by
      rw [dist_eq_norm, show z - (1 - t / 5 : ℝ) • z = (t / 5 : ℝ) • z by
        rw [sub_smul, one_smul, sub_sub_cancel], norm_smul, hz,
        Real.norm_of_nonneg (by linarith)]
      ring
    refine ⟨(1 - t / 5 : ℝ) • z, ?_, by rw [hdist]; linarith⟩
    unfold annulus
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, hnorm]
      linarith
    · rw [mem_closedBall, dist_zero_right, hnorm, not_le]
      linarith
  · intro hint
    have hT5 : fixedT ⊆ ball (0 : ℂ) 5 := fun w hw => (fixedT_subset_annulus hw).1
    have hz' := hT5 (interior_subset hint)
    rw [mem_ball, dist_zero_right, hz] at hz'
    exact lt_irrefl _ hz'

/-- The fixed sets form a pinch-point configuration (`Defs/Geometry.lean`). -/
theorem isPinchPointConfiguration_fixed :
    IsPinchPointConfiguration fixedU fixedT fixedQ' fixedQ where
  isOpen_U := isOpen_ball
  isConnected_U := ⟨⟨pinchCentreA, mem_ball_self (by norm_num)⟩, (convex_ball _ _).isPreconnected⟩
  isOpen_T := isOpen_fixedT
  isConnected_T := isConnected_fixedT
  isOpen_Q' := isOpen_ball
  isConnected_Q' := ⟨⟨pinchCentreB, mem_ball_self (by norm_num)⟩, (convex_ball _ _).isPreconnected⟩
  isOpen_Q := isOpen_ball
  isConnected_Q := ⟨⟨pinchCentreB, mem_ball_self (by norm_num)⟩, (convex_ball _ _).isPreconnected⟩
  closure_U_subset := fixedPinch_closure_U
  closure_Q'_subset := fixedPinch_closure_Q'
  exists_eq_ball := ⟨pinchCentreA, 1 / 100, rfl⟩
  U_subset := fixedU_subset_annulus
  Q_subset := fixedQ_subset
  T_subset := fixedT_subset_annulus
  sphere_subset_frontier := sphere_subset_frontier_fixedT

/-- Existence of a pinch-point configuration, the existential witness of Lemma 11.12
(`PinchEventPositiveProbabilityStmt`, `HarmonicBalls/Draft/Section11.lean:246`). -/
theorem exists_isPinchPointConfiguration :
    ∃ U T Q' Q : Set ℂ, IsPinchPointConfiguration U T Q' Q :=
  ⟨fixedU, fixedT, fixedQ', fixedQ, isPinchPointConfiguration_fixed⟩

#print axioms isPinchPointConfiguration_fixed
#print axioms exists_isPinchPointConfiguration

end HarmonicBalls
