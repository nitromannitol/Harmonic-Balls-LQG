import HarmonicBalls.Defs.Geometry

/-!
# An explicit pinch-point configuration (Lemma 11.13, step 1)

`ManyPinchScalesStmt` (`HarmonicBalls/Draft/Section11.lean:259`) begins with `∃ U T Q' Q, IsPinchPointConfiguration U T Q' Q`.
This file proves that existence for one explicit deterministic geometry, fixed before all other parameters (with `c = 3/2`):
`U = B_{1/100}(3/2)`, `T = B_{1/10}(3/2) ∪ S ∪ 𝔸_{24/5,5}` with the strip `S = {3/2 < x < 49/10, |y| < 1/50}`,
`Q' = B_{1/100}(-22/5)`, `Q = B_{1/50}(-22/5)`. The fields checked are those of the structure `IsPinchPointConfiguration`
(`HarmonicBalls/Defs/Geometry.lean:190`); the keyhole shape of the paper's figure is not part of that structure.
-/

open Metric Set

namespace FirstPassS11i

lemma norm_ofReal_eq {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ = r := by
  rw [Complex.norm_real, Real.norm_of_nonneg hr]

/-- Norm bounds for a point of a ball. -/
lemma norm_bounds_of_mem_ball {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) :
    ‖c‖ - r < ‖z‖ ∧ ‖z‖ < ‖c‖ + r := by
  rw [mem_ball, dist_eq_norm] at hz
  have h1 := norm_sub_norm_le z c
  have h2 := norm_sub_norm_le c z
  rw [norm_sub_rev c z] at h2
  constructor <;> linarith

/-- Real part bounds for a point of a ball. -/
lemma re_bounds_of_mem_ball {c z : ℂ} {r : ℝ} (hz : z ∈ ball c r) :
    c.re - r < z.re ∧ z.re < c.re + r := by
  rw [mem_ball, dist_eq_norm] at hz
  obtain ⟨h1, h2⟩ := abs_le.1 (Complex.abs_re_le_norm (z - c))
  rw [Complex.sub_re] at h1 h2
  constructor <;> linarith

/-- The open strip `{3/2 < x < 49/10, |y| < 1/50}` joining the disc of `U` to the outer annulus. -/
def pinchStrip : Set ℂ :=
  {z | 3 / 2 < z.re} ∩ {z | z.re < 49 / 10} ∩ {z | -(1 / 50) < z.im} ∩ {z | z.im < 1 / 50}

/-- The domain `T = B_{1/10}(3/2) ∪ S ∪ 𝔸_{24/5,5}`. -/
def pinchT : Set ℂ :=
  ball ((3 / 2 : ℝ) : ℂ) (1 / 10) ∪ pinchStrip ∪ HarmonicBalls.annulus 0 (24 / 5) 5

lemma pinchStrip_mem {z : ℂ} :
    z ∈ pinchStrip ↔ 3 / 2 < z.re ∧ z.re < 49 / 10 ∧ -(1 / 50) < z.im ∧ z.im < 1 / 50 := by
  unfold pinchStrip
  simp only [mem_inter_iff, Set.mem_ofPred_eq, and_assoc]

lemma isOpen_pinchStrip : IsOpen pinchStrip := by
  unfold pinchStrip
  exact (((isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)).inter
    (isOpen_lt continuous_const Complex.continuous_im)).inter
    (isOpen_lt Complex.continuous_im continuous_const)

lemma re_isLinear : IsLinearMap ℝ (fun z : ℂ => z.re) :=
  ⟨fun x y => Complex.add_re x y, fun c x => by simp⟩

lemma im_isLinear : IsLinearMap ℝ (fun z : ℂ => z.im) :=
  ⟨fun x y => Complex.add_im x y, fun c x => by simp⟩

lemma convex_pinchStrip : Convex ℝ pinchStrip := by
  unfold pinchStrip
  exact (((convex_halfSpace_gt re_isLinear _).inter (convex_halfSpace_lt re_isLinear _)).inter
    (convex_halfSpace_gt im_isLinear _)).inter (convex_halfSpace_lt im_isLinear _)

lemma mem_annulus_iff {z : ℂ} {r₁ r₂ : ℝ} :
    z ∈ HarmonicBalls.annulus 0 r₁ r₂ ↔ ‖z‖ < r₂ ∧ r₁ < ‖z‖ := by
  unfold HarmonicBalls.annulus
  simp only [mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le]

/-- The annulus `𝔸_{24/5,5}` is the image of `(24/5, 5) × ℝ` under `(t, θ) ↦ t e^{iθ}`. -/
lemma annulus_eq_image :
    HarmonicBalls.annulus 0 (24 / 5) 5 =
      (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ) * Complex.exp (((p.2 : ℝ) : ℂ) * Complex.I)) ''
        (Ioo (24 / 5) 5 ×ˢ (univ : Set ℝ)) := by
  ext z
  rw [mem_annulus_iff]
  constructor
  · rintro ⟨h5, h24⟩
    refine ⟨(‖z‖, Complex.arg z), ⟨⟨h24, h5⟩, mem_univ _⟩, ?_⟩
    exact Complex.norm_mul_exp_arg_mul_I z
  · rintro ⟨⟨t, θ⟩, hmem, rfl⟩
    obtain ⟨⟨ht1, ht2⟩, -⟩ := hmem
    dsimp only at ht1 ht2 ⊢
    have hnorm : ‖((t : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I)‖ = t := by
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_ofReal_eq (by linarith)]
    rw [hnorm]
    exact ⟨ht2, ht1⟩

lemma isConnected_annulus : IsConnected (HarmonicBalls.annulus 0 (24 / 5) 5) := by
  rw [annulus_eq_image]
  refine IsConnected.image ((isConnected_Ioo (by norm_num)).prod isConnected_univ) _ ?_
  exact Continuous.continuousOn (by fun_prop)

lemma pinchT_isConnected : IsConnected pinchT := by
  unfold pinchT
  have hball : IsConnected (ball ((3 / 2 : ℝ) : ℂ) (1 / 10)) :=
    (convex_ball _ _).isConnected ⟨_, mem_ball_self (by norm_num)⟩
  have hxs : ((31 / 20 : ℝ) : ℂ) ∈ pinchStrip := by
    refine pinchStrip_mem.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> norm_num
  have hxb : ((31 / 20 : ℝ) : ℂ) ∈ ball ((3 / 2 : ℝ) : ℂ) (1 / 10) := by
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hA : IsConnected (ball ((3 / 2 : ℝ) : ℂ) (1 / 10) ∪ pinchStrip) :=
    IsConnected.union ⟨_, hxb, hxs⟩ hball (convex_pinchStrip.isConnected ⟨_, hxs⟩)
  have hys : ((97 / 20 : ℝ) : ℂ) ∈ pinchStrip := by
    refine pinchStrip_mem.2 ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> norm_num
  have hya : ((97 / 20 : ℝ) : ℂ) ∈ HarmonicBalls.annulus 0 (24 / 5) 5 := by
    rw [mem_annulus_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by norm_num)]
    norm_num
  exact IsConnected.union ⟨_, Or.inr hys, hya⟩ hA isConnected_annulus

lemma norm_ofReal_three_halves : ‖((3 / 2 : ℝ) : ℂ)‖ = 3 / 2 :=
  norm_ofReal_eq (r := 3 / 2) (by norm_num)

lemma norm_ofReal_neg_twentytwo_fifths : ‖((-22 / 5 : ℝ) : ℂ)‖ = 22 / 5 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg (show (-22 / 5 : ℝ) < 0 by norm_num)]
  norm_num

lemma isOpen_annulus : IsOpen (HarmonicBalls.annulus 0 (24 / 5) 5) := by
  unfold HarmonicBalls.annulus
  exact isOpen_ball.sdiff isClosed_closedBall

lemma isOpen_pinchT : IsOpen pinchT :=
  (isOpen_ball.union isOpen_pinchStrip).union isOpen_annulus

/-- Norm bounds on the strip: `1 < |z| < 5`. -/
lemma strip_norm_bounds {z : ℂ} (hz : z ∈ pinchStrip) : 1 < ‖z‖ ∧ ‖z‖ < 5 := by
  obtain ⟨h1, h2, h3, h4⟩ := pinchStrip_mem.1 hz
  have hre : z.re ≤ ‖z‖ := (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have him : |z.im| < 1 / 50 := abs_lt.2 ⟨h3, h4⟩
  have hn : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hre' : |z.re| = z.re := abs_of_pos (by linarith)
  constructor <;> linarith

lemma pinchT_subset_annulus : pinchT ⊆ HarmonicBalls.annulus 0 1 5 := by
  intro z hz
  unfold pinchT at hz
  rcases hz with (hz | hz) | hz
  · obtain ⟨h1, h2⟩ := norm_bounds_of_mem_ball hz
    rw [norm_ofReal_three_halves] at h1 h2
    exact mem_annulus_iff.2 ⟨by linarith, by linarith⟩
  · obtain ⟨h1, h2⟩ := strip_norm_bounds hz
    exact mem_annulus_iff.2 ⟨by linarith, by linarith⟩
  · obtain ⟨h1, h2⟩ := mem_annulus_iff.1 hz
    exact mem_annulus_iff.2 ⟨h1, by linarith⟩

/-- The closed set `{0 ≤ Re z} ∪ {46/10 ≤ |z|}` contains `T`, and so its closure. -/
lemma closure_pinchT_subset : closure pinchT ⊆ {z : ℂ | 0 ≤ z.re} ∪ {z : ℂ | 46 / 10 ≤ ‖z‖} := by
  apply closure_minimal _ ((isClosed_le continuous_const Complex.continuous_re).union
    (isClosed_le continuous_const continuous_norm))
  intro z hz
  unfold pinchT at hz
  rcases hz with (hz | hz) | hz
  · obtain ⟨h1, -⟩ := re_bounds_of_mem_ball hz
    rw [Complex.ofReal_re] at h1
    exact Or.inl (show (0 : ℝ) ≤ z.re by linarith)
  · obtain ⟨h1, -⟩ := pinchStrip_mem.1 hz
    exact Or.inl (show (0 : ℝ) ≤ z.re by linarith)
  · obtain ⟨-, h2⟩ := mem_annulus_iff.1 hz
    exact Or.inr (show (46 / 10 : ℝ) ≤ ‖z‖ by linarith)

lemma pinchQ_subset :
    ball ((-22 / 5 : ℝ) : ℂ) (1 / 50) ⊆ HarmonicBalls.annulus 0 4 5 \ closure pinchT := by
  intro z hz
  obtain ⟨h1, h2⟩ := norm_bounds_of_mem_ball hz
  obtain ⟨h3, h4⟩ := re_bounds_of_mem_ball hz
  rw [norm_ofReal_neg_twentytwo_fifths] at h1 h2
  rw [Complex.ofReal_re] at h3 h4
  refine ⟨mem_annulus_iff.2 ⟨by linarith, by linarith⟩, fun hcl => ?_⟩
  rcases closure_pinchT_subset hcl with h | h
  · have h' : (0 : ℝ) ≤ z.re := h
    linarith
  · have h' : (46 / 10 : ℝ) ≤ ‖z‖ := h
    linarith

lemma closure_pinchU_subset :
    closure (ball ((3 / 2 : ℝ) : ℂ) (1 / 100)) ⊆ pinchT :=
  fun z hz => Or.inl (Or.inl
    ((closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num : (1 / 100 : ℝ) < 1 / 10))) hz))

lemma closure_pinchQ'_subset :
    closure (ball ((-22 / 5 : ℝ) : ℂ) (1 / 100)) ⊆ ball ((-22 / 5 : ℝ) : ℂ) (1 / 50) :=
  closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num : (1 / 100 : ℝ) < 1 / 50))

lemma pinchU_subset :
    ball ((3 / 2 : ℝ) : ℂ) (1 / 100) ⊆ HarmonicBalls.annulus 0 1 2 := by
  intro z hz
  obtain ⟨h1, h2⟩ := norm_bounds_of_mem_ball hz
  rw [norm_ofReal_three_halves] at h1 h2
  exact mem_annulus_iff.2 ⟨by linarith, by linarith⟩

lemma pinchT_sphere_subset_frontier : sphere (0 : ℂ) 5 ⊆ frontier pinchT := by
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  have hcl : z ∈ closure pinchT := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hδpos : 0 < min (ε / 10) (1 / 100 : ℝ) := lt_min (by linarith) (by norm_num)
    have hδle : min (ε / 10) (1 / 100 : ℝ) ≤ 1 / 100 := min_le_right _ _
    have hδε : min (ε / 10) (1 / 100 : ℝ) ≤ ε / 10 := min_le_left _ _
    refine ⟨((1 - min (ε / 10) (1 / 100 : ℝ) : ℝ) : ℂ) * z, ?_, ?_⟩
    · unfold pinchT
      refine Or.inr (mem_annulus_iff.2 ⟨?_, ?_⟩)
      · rw [norm_mul, norm_ofReal_eq (r := 1 - min (ε / 10) (1 / 100 : ℝ)) (by linarith), hz]
        linarith
      · rw [norm_mul, norm_ofReal_eq (r := 1 - min (ε / 10) (1 / 100 : ℝ)) (by linarith), hz]
        linarith
    · rw [dist_eq_norm]
      have hsub : z - ((1 - min (ε / 10) (1 / 100 : ℝ) : ℝ) : ℂ) * z
          = ((min (ε / 10) (1 / 100 : ℝ) : ℝ) : ℂ) * z := by
        push_cast
        ring
      rw [hsub, norm_mul, norm_ofReal_eq hδpos.le, hz]
      linarith
  refine ⟨hcl, ?_⟩
  rw [isOpen_pinchT.interior_eq]
  intro hzT
  have := (mem_annulus_iff.1 (pinchT_subset_annulus hzT)).1
  linarith

theorem exists_isPinchPointConfiguration :
    ∃ U T Q' Q : Set ℂ, HarmonicBalls.IsPinchPointConfiguration U T Q' Q :=
  ⟨ball ((3 / 2 : ℝ) : ℂ) (1 / 100), pinchT, ball ((-22 / 5 : ℝ) : ℂ) (1 / 100),
    ball ((-22 / 5 : ℝ) : ℂ) (1 / 50),
    { isOpen_U := isOpen_ball
      isConnected_U := (convex_ball _ _).isConnected ⟨_, mem_ball_self (by norm_num)⟩
      isOpen_T := isOpen_pinchT
      isConnected_T := pinchT_isConnected
      isOpen_Q' := isOpen_ball
      isConnected_Q' := (convex_ball _ _).isConnected ⟨_, mem_ball_self (by norm_num)⟩
      isOpen_Q := isOpen_ball
      isConnected_Q := (convex_ball _ _).isConnected ⟨_, mem_ball_self (by norm_num)⟩
      closure_U_subset := closure_pinchU_subset
      closure_Q'_subset := closure_pinchQ'_subset
      exists_eq_ball := ⟨_, _, rfl⟩
      U_subset := pinchU_subset
      Q_subset := pinchQ_subset
      T_subset := pinchT_subset_annulus
      sphere_subset_frontier := pinchT_sphere_subset_frontier }⟩

end FirstPassS11i
