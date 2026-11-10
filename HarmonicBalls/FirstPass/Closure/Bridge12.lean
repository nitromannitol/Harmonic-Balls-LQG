import HarmonicBalls.FirstPass.S11i.Faithful

/-!
# Bridge from the corrected Lemma 11.13 to `ManyPinchScalesStmt` (fp-closure-bridge-1-2, z7)

FIRST-PASS CLOSURE, deterministic (no probability). Source: `notes/fp-gaps/CHATGPT-hb-1-2-bridge.md` §1 (projection and
an explicit buffered keyhole geometry) and §3 (the bridge), ChatGPT chat 178, operator note 2026-11-10 05:42 UTC.

`CorrectedLemma11_13Stmt` (corrected `[C42]`) quantifies over every buffered geometry, while `ManyPinchScalesStmt`
asks for one pinch point configuration. Fixing one buffered geometry gives the bridge.

* `HarmonicBalls.IsBufferedPinchGeometry.toPinchPointConfiguration`: the projection (no hypothesis).
* `HarmonicBalls.Closure.exists_bufferedPinchGeometry_of_connected`: the explicit geometry of §1, with the connectedness of
  `T` as the hypothesis `hT`. The closed form `HarmonicBalls.Closure.exists_bufferedPinchGeometry` is to follow when
  `isConnected_annulus_diff_closedBall` (`Closure/Bridge12Connected.lean`, z4) is committed.
* `HarmonicBalls.Closure.manyPinchScales_of_corrected_of_connected`: `CorrectedLemma11_13Stmt` implies
  `ManyPinchScalesStmt`, choosing the geometry above (closed form to follow with `hT`).

The `Defs` of the keyhole geometry are the paper's `𝔸_{r₁,r₂}(z) = B_{r₂}(z) \ closure B_{r₁}(z)` (`HarmonicBalls.annulus`).
-/

universe u

namespace HarmonicBalls

open Set Metric

/-- The projection of a buffered pinch geometry to a pinch point configuration. It forgets `V`, `W`, `δ` and the six
buffer conditions; `closure U ⊆ T` follows from the chain `U ⋐ V ⋐ W`, `closure W ⊆ T` of the buffers. -/
theorem IsBufferedPinchGeometry.toPinchPointConfiguration {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) : IsPinchPointConfiguration U T Q' Q := by
  obtain ⟨c, ρU, ρV, ρW, hU, hV, hW⟩ := h.concentric
  have hpos : (0 : ℝ) < 10 * δ := by linarith [h.delta_pos]
  have hUV : closure U ⊆ V := fun x hx =>
    h.buffer_U (subset_closure (self_subset_thickening hpos (closure U) hx))
  have hVW : V ⊆ W := fun x hx =>
    h.buffer_V (subset_closure (self_subset_thickening hpos (closure V) (subset_closure hx)))
  have hWT : closure W ⊆ T := fun x hx =>
    (h.buffer_W (subset_closure (self_subset_thickening hpos (closure W) hx))).1
  have hUc : IsConnected U := by
    rw [hU]
    exact (convex_ball c ρU).isConnected (by rw [← hU]; exact h.U_nonempty)
  exact
    { isOpen_U := h.isOpen_U
      isConnected_U := hUc
      isOpen_T := h.isOpen_T
      isConnected_T := h.isConnected_T
      isOpen_Q' := h.isOpen_Q'
      isConnected_Q' := h.isConnected_Q'
      isOpen_Q := h.isOpen_Q
      isConnected_Q := h.isConnected_Q
      closure_U_subset := fun x hx => hWT (subset_closure (hVW (hUV hx)))
      closure_Q'_subset := h.closure_Q'_subset_Q
      exists_eq_ball := ⟨c, ρU, hU⟩
      U_subset := h.U_subset
      Q_subset := fun x hx => h.closure_Q_subset (subset_closure hx)
      T_subset := h.T_subset
      sphere_subset_frontier := fun z hz => by
        rw [frontier, h.isOpen_T.interior_eq]
        refine ⟨h.sphere_subset_closure_T hz, fun hzT => ?_⟩
        have hT5 : z ∈ ball (0 : ℂ) 5 \ closedBall (0 : ℂ) 1 := h.T_subset hzT
        have h5 : dist z 0 < 5 := mem_ball.1 hT5.1
        have hz5 : dist z 0 = 5 := mem_sphere.1 hz
        linarith }

namespace Closure

/-! ## Elementary distance bounds -/

/-- Triangle inequality in the form used throughout: if `dist c d = s` and `dist z c ≤ r` then
`s - r ≤ dist z d ≤ s + r`. -/
lemma bridge_dist_bounds {z c d : ℂ} {s r : ℝ} (hcd : dist c d = s) (hz : dist z c ≤ r) :
    s - r ≤ dist z d ∧ dist z d ≤ s + r := by
  have h := abs_dist_sub_le z c d
  rw [hcd] at h
  have h' := abs_le.1 (h.trans hz)
  constructor <;> linarith [h'.1, h'.2]

/-- A point `w` at distance `< r` from `a` has `dist w d` within `r` of `dist a d`. -/
lemma bridge_near {w a : ℂ} {r : ℝ} (hwa : dist w a < r) (d : ℂ) :
    dist a d - r ≤ dist w d ∧ dist w d ≤ dist a d + r :=
  bridge_dist_bounds (s := dist a d) rfl hwa.le

lemma bridge_dist_c1 : dist (3 / 2 : ℂ) 0 = 3 / 2 := by
  rw [dist_zero_right, show (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]

lemma bridge_dist_c2 : dist (-9 / 2 : ℂ) 0 = 9 / 2 := by
  rw [dist_zero_right, show (-9 / 2 : ℂ) = ((-9 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Real.norm_eq_abs,
    abs_of_neg (by norm_num : (-9 / 2 : ℝ) < 0)]
  norm_num

lemma bridge_dist_c12 : dist (3 / 2 : ℂ) (-9 / 2) = 6 := by
  rw [dist_eq_norm, show (3 / 2 : ℂ) - (-9 / 2) = ((6 : ℝ) : ℂ) by norm_num, Complex.norm_real,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]

/-- The open annulus `𝔸_{r₁,r₂}(z)` in distance form. -/
lemma bridge_mem_annulus {c : ℂ} {r₁ r₂ : ℝ} {w : ℂ} :
    w ∈ annulus c r₁ r₂ ↔ dist w c < r₂ ∧ r₁ < dist w c := by
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le]

/-- Sub-balls of the disk `B_{3/2}(0)`-type sets: `B_ρ(3/2) ⊆ 𝔸_{1,2}(0)` for `ρ < 1/2`. -/
lemma bridge_ball_sub_annulus {ρ : ℝ} (hρ : ρ < 1 / 2) : ball (3 / 2 : ℂ) ρ ⊆ annulus 0 1 2 := by
  intro z hz
  obtain ⟨h1, h2⟩ := bridge_dist_bounds bridge_dist_c1 (mem_ball.1 hz).le
  exact bridge_mem_annulus.2 ⟨by linarith, by linarith⟩

/-! ## The closed box and the keyhole set `T` -/

/-- The closed set `{w | dist w 0 ≤ p, q ≤ dist w 0, s ≤ dist w (-9/2)}` (an intersection of three closed sets). -/
def bridgeBox (p q s : ℝ) : Set ℂ :=
  {w | dist w 0 ≤ p} ∩ ({w | q ≤ dist w 0} ∩ {w | s ≤ dist w (-9 / 2 : ℂ)})

lemma isClosed_bridgeBox (p q s : ℝ) : IsClosed (bridgeBox p q s) := by
  unfold bridgeBox
  exact (isClosed_le (continuous_id.dist continuous_const) continuous_const).inter
    ((isClosed_le continuous_const (continuous_id.dist continuous_const)).inter
      (isClosed_le continuous_const (continuous_id.dist continuous_const)))

lemma mem_bridgeBox {p q s : ℝ} {w : ℂ} :
    w ∈ bridgeBox p q s ↔ dist w 0 ≤ p ∧ q ≤ dist w 0 ∧ s ≤ dist w (-9 / 2 : ℂ) :=
  Iff.rfl

/-- The keyhole set of the §1 geometry: `T = 𝔸_{6/5,5}(0) \ closedBall (-9/2) (1/4)`. -/
abbrev bridgeT : Set ℂ := annulus 0 (6 / 5) 5 \ closedBall (-9 / 2 : ℂ) (1 / 4)

lemma mem_bridgeT {w : ℂ} :
    w ∈ bridgeT ↔ (dist w 0 < 5 ∧ 6 / 5 < dist w 0) ∧ 1 / 4 < dist w (-9 / 2 : ℂ) := by
  simp only [bridgeT, mem_sdiff, bridge_mem_annulus, mem_closedBall, not_le]

lemma isOpen_bridgeT : IsOpen bridgeT := by
  unfold bridgeT annulus
  exact (isOpen_ball.sdiff isClosed_closedBall).sdiff isClosed_closedBall

lemma bridgeT_sub_box : bridgeT ⊆ bridgeBox 5 (6 / 5) (1 / 4) := fun w hw => by
  obtain ⟨⟨h5, h6⟩, h7⟩ := mem_bridgeT.1 hw
  exact mem_bridgeBox.2 ⟨h5.le, h6.le, h7.le⟩

lemma closure_bridgeT_sub_box : closure bridgeT ⊆ bridgeBox 5 (6 / 5) (1 / 4) :=
  closure_minimal bridgeT_sub_box (isClosed_bridgeBox _ _ _)

lemma closure_bridgeT_sub_annulus : closure bridgeT ⊆ annulus 0 1 6 := fun w hw => by
  obtain ⟨h1, h2, _⟩ := mem_bridgeBox.1 (closure_bridgeT_sub_box hw)
  exact bridge_mem_annulus.2 ⟨by linarith, by linarith⟩

lemma bridgeT_sub_annulus : bridgeT ⊆ annulus 0 1 5 := fun w hw => by
  obtain ⟨⟨h5, h6⟩, _⟩ := mem_bridgeT.1 hw
  exact bridge_mem_annulus.2 ⟨h5, by linarith⟩

/-- `W` is inside `T` and `𝔸_{1,2}`: the closed disk `B̄_{3/2}(3/50 + s)` lies in `T ∩ 𝔸_{1,2}(0)` for `0 ≤ s ≤ 1/20`. -/
lemma bridge_W_mem {s : ℝ} (hs : s ≤ 1 / 20) {w : ℂ} (hw : dist w (3 / 2 : ℂ) ≤ 3 / 50 + s) :
    w ∈ bridgeT ∩ annulus 0 1 2 := by
  obtain ⟨h1, h2⟩ := bridge_dist_bounds bridge_dist_c1 hw
  obtain ⟨h3, _⟩ := bridge_dist_bounds bridge_dist_c12 hw
  exact ⟨mem_bridgeT.2 ⟨⟨by linarith, by linarith⟩, by linarith⟩, bridge_mem_annulus.2 ⟨by linarith, by linarith⟩⟩

/-- The sphere `∂B₅` lies in `closure T`: points `(1 - t) z` with small `t > 0` lie in `T`. -/
lemma sphere_sub_closure_bridgeT : sphere (0 : ℂ) 5 ⊆ closure bridgeT := by
  intro z hz
  have hz5 : dist z 0 = 5 := mem_sphere.1 hz
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨t, ht0, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ 1 / 100 ∧ t ≤ ε / 10 :=
    ⟨min (ε / 10) (1 / 100), lt_min (by linarith) (by norm_num), min_le_right _ _, min_le_left _ _⟩
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  have hnb : dist (((1 - t : ℝ) : ℂ) * z) 0 = (1 - t) * 5 := by
    rw [dist_zero_right, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht1', ← dist_zero_right, hz5]
  refine ⟨((1 - t : ℝ) : ℂ) * z, ?_, ?_⟩
  · have h3 := abs_dist_sub_le (((1 - t : ℝ) : ℂ) * z) (-9 / 2 : ℂ) 0
    rw [hnb, bridge_dist_c2] at h3
    have h4 := le_abs_self ((1 - t) * 5 - 9 / 2)
    rw [mem_bridgeT, hnb]
    exact ⟨⟨by linarith, by linarith⟩, by linarith⟩
  · have hzb : z - ((1 - t : ℝ) : ℂ) * z = ((t : ℝ) : ℂ) * z := by
      push_cast
      ring
    rw [dist_eq_norm, hzb, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le, ← dist_zero_right, hz5]
    linarith

/-- The closure of `T` lies in `∂B_{6/5}`-type closed box, hence in `𝔸_{1,6}(0)`. -/
lemma bridge_thickening_closure {A F Y : Set ℂ} {r : ℝ} (hF : IsClosed F)
    (hA : ∀ a ∈ A, ∀ w, dist w a < r → w ∈ F) (hFY : F ⊆ Y) : closure (thickening r A) ⊆ Y := by
  have h1 : thickening r A ⊆ F := fun w hw => by
    obtain ⟨a, ha, hwa⟩ := mem_thickening_iff.1 hw
    exact hA a ha w hwa
  exact (closure_minimal h1 hF).trans hFY

/-- The buffer of a ball: `closure (thickening r (closure (ball c ρ)))` lies in any `Y ⊇ B̄_{ρ + r}(c)`. -/
lemma bridge_buffer_ball {c : ℂ} {ρ r : ℝ} {Y : Set ℂ} (hY : closedBall c (ρ + r) ⊆ Y) :
    closure (thickening r (closure (ball c ρ))) ⊆ Y := by
  refine bridge_thickening_closure (F := closedBall c (ρ + r)) isClosed_closedBall ?_ hY
  intro a ha w hwa
  have ha' : dist a c ≤ ρ :=
    mem_closedBall.1 (closure_minimal ball_subset_closedBall isClosed_closedBall ha)
  rw [mem_closedBall]
  linarith [dist_triangle w a c]

/-! ## The six buffer conditions of the §1 geometry (`δ = 1/100000`, so `r = 10 δ = 1/10000`) -/

lemma bridge_buffer_U {r : ℝ} (hr : r ≤ 1 / 1000) :
    closure (thickening r (closure (ball (3 / 2 : ℂ) (1 / 50)))) ⊆ ball (3 / 2 : ℂ) (1 / 25) :=
  bridge_buffer_ball (Metric.closedBall_subset_ball (by linarith))

lemma bridge_buffer_V {r : ℝ} (hr : r ≤ 1 / 1000) :
    closure (thickening r (closure (ball (3 / 2 : ℂ) (1 / 25)))) ⊆ ball (3 / 2 : ℂ) (3 / 50) :=
  bridge_buffer_ball (Metric.closedBall_subset_ball (by linarith))

lemma bridge_buffer_W {r : ℝ} (hr : r ≤ 1 / 1000) :
    closure (thickening r (closure (ball (3 / 2 : ℂ) (3 / 50)))) ⊆ bridgeT ∩ annulus 0 1 2 :=
  bridge_buffer_ball (fun _ hw => bridge_W_mem (by linarith) (mem_closedBall.1 hw))

lemma bridge_buffer_Q' {r : ℝ} (hr : r ≤ 1 / 1000) :
    closure (thickening r (closure (ball (-9 / 2 : ℂ) (1 / 16)))) ⊆ ball (-9 / 2 : ℂ) (1 / 8) :=
  bridge_buffer_ball (Metric.closedBall_subset_ball (by linarith))

lemma bridge_buffer_T {r : ℝ} (hr : r ≤ 1 / 1000) :
    closure (thickening r (closure bridgeT)) ⊆ annulus 0 1 6 := by
  refine bridge_thickening_closure (F := bridgeBox (5 + r) (6 / 5 - r) (1 / 4 - r))
    (isClosed_bridgeBox _ _ _) ?_ ?_
  · intro a ha w hwa
    obtain ⟨h1, h2, h3⟩ := mem_bridgeBox.1 (closure_bridgeT_sub_box ha)
    obtain ⟨n1, n2⟩ := bridge_near hwa 0
    obtain ⟨m1, m2⟩ := bridge_near hwa (-9 / 2 : ℂ)
    exact mem_bridgeBox.2 ⟨by linarith, by linarith, by linarith⟩
  · intro w hw
    obtain ⟨h1, h2, _⟩ := mem_bridgeBox.1 hw
    exact bridge_mem_annulus.2 ⟨by linarith, by linarith⟩

lemma bridge_buffer_Q {r : ℝ} (hr : r ≤ 1 / 1000) :
    closure (thickening r (closure (ball (-9 / 2 : ℂ) (1 / 8)))) ⊆
      annulus 0 4 5 \ thickening r (closure bridgeT) := by
  refine bridge_thickening_closure (F := closedBall (-9 / 2 : ℂ) (1 / 8 + r)) isClosed_closedBall ?_ ?_
  · intro a ha w hwa
    have ha' : dist a (-9 / 2 : ℂ) ≤ 1 / 8 :=
      mem_closedBall.1 (closure_minimal ball_subset_closedBall isClosed_closedBall ha)
    obtain ⟨n1, n2⟩ := bridge_near hwa (-9 / 2 : ℂ)
    rw [mem_closedBall]
    linarith
  · intro w hw
    rw [mem_closedBall] at hw
    obtain ⟨h1, h2⟩ := bridge_dist_bounds bridge_dist_c2 hw
    refine ⟨bridge_mem_annulus.2 ⟨by linarith, by linarith⟩, ?_⟩
    intro hw'
    obtain ⟨a, ha, hwa⟩ := Metric.mem_thickening_iff.1 hw'
    obtain ⟨_, _, hb3⟩ := mem_bridgeBox.1 (closure_bridgeT_sub_box ha)
    obtain ⟨m1, _⟩ := bridge_near hwa (-9 / 2 : ℂ)
    linarith

/-- The closure of the disk `B_{1/8}(-9/2)` avoids `closure T` and lies in `𝔸_{4,5}(0)`. -/
lemma bridge_closure_Q_sub : closure (ball (-9 / 2 : ℂ) (1 / 8)) ⊆ annulus 0 4 5 \ closure bridgeT := by
  intro z hz
  have hzc : dist z (-9 / 2 : ℂ) ≤ 1 / 8 :=
    mem_closedBall.1 (closure_minimal ball_subset_closedBall isClosed_closedBall hz)
  obtain ⟨h1, h2⟩ := bridge_dist_bounds bridge_dist_c2 hzc
  refine ⟨bridge_mem_annulus.2 ⟨by linarith, by linarith⟩, ?_⟩
  intro hzT
  obtain ⟨_, _, hb3⟩ := mem_bridgeBox.1 (closure_bridgeT_sub_box hzT)
  linarith

/-! ## The bridge -/

/-- An explicit buffered keyhole geometry (§1 of the bridge note): `U = B(3/2, 1/50)`, `V = B(3/2, 1/25)`,
`W = B(3/2, 3/50)`, `T = 𝔸_{6/5,5}(0) \ B̄(-9/2, 1/4)`, `Q' = B(-9/2, 1/16)`, `Q = B(-9/2, 1/8)`, `δ = 1/100000`.
The connectedness of `T` is the hypothesis `hT` (to be discharged by `isConnected_annulus_diff_closedBall`). -/
theorem exists_bufferedPinchGeometry_of_connected
    (hT : IsConnected (annulus 0 (6 / 5) 5 \ closedBall (-9 / 2 : ℂ) (1 / 4))) :
    ∃ (U V W T Q' Q : Set ℂ) (δ₀ : ℝ), IsBufferedPinchGeometry U V W T Q' Q δ₀ := by
  refine ⟨ball (3 / 2 : ℂ) (1 / 50), ball (3 / 2 : ℂ) (1 / 25), ball (3 / 2 : ℂ) (3 / 50), bridgeT,
    ball (-9 / 2 : ℂ) (1 / 16), ball (-9 / 2 : ℂ) (1 / 8), 1 / 100000, ?_⟩
  have hW : closure (ball (3 / 2 : ℂ) (3 / 50)) ⊆ bridgeT := fun w hw =>
    (bridge_W_mem (s := 0) (by norm_num)
      (w := w) (by linarith [mem_closedBall.1 (closure_minimal ball_subset_closedBall isClosed_closedBall hw)])).1
  exact
    { isOpen_U := isOpen_ball
      isOpen_V := isOpen_ball
      isOpen_W := isOpen_ball
      isOpen_T := isOpen_bridgeT
      isOpen_Q' := isOpen_ball
      isOpen_Q := isOpen_ball
      isConnected_T := hT
      isConnected_Q' := (convex_ball _ _).isConnected (nonempty_ball.2 (by norm_num))
      isConnected_Q := (convex_ball _ _).isConnected (nonempty_ball.2 (by norm_num))
      concentric := ⟨3 / 2, 1 / 50, 1 / 25, 3 / 50, rfl, rfl, rfl⟩
      U_nonempty := ⟨3 / 2, mem_ball_self (by norm_num)⟩
      U_subset := bridge_ball_sub_annulus (by norm_num)
      V_subset := bridge_ball_sub_annulus (by norm_num)
      W_subset := bridge_ball_sub_annulus (by norm_num)
      closure_W_subset_T := hW
      T_subset := bridgeT_sub_annulus
      closure_T_subset := closure_bridgeT_sub_annulus
      sphere_subset_closure_T := sphere_sub_closure_bridgeT
      closure_Q'_subset_Q :=
        (closure_minimal ball_subset_closedBall isClosed_closedBall).trans
          (Metric.closedBall_subset_ball (by norm_num))
      closure_Q_subset := bridge_closure_Q_sub
      delta_pos := by norm_num
      delta_lt := by norm_num
      buffer_T := bridge_buffer_T (by norm_num)
      buffer_U := bridge_buffer_U (by norm_num)
      buffer_V := bridge_buffer_V (by norm_num)
      buffer_W := bridge_buffer_W (by norm_num)
      buffer_Q' := bridge_buffer_Q' (by norm_num)
      buffer_Q := bridge_buffer_Q (by norm_num) }

/-- `CorrectedLemma11_13Stmt` implies `ManyPinchScalesStmt`: fix the buffered geometry of
`exists_bufferedPinchGeometry_of_connected` and forget `V, W, δ₀` (§3 of the bridge note). -/
theorem manyPinchScales_of_corrected_of_connected
    (hT : IsConnected (annulus 0 (6 / 5) 5 \ closedBall (-9 / 2 : ℂ) (1 / 4)))
    (h : CorrectedLemma11_13Stmt.{u}) : ManyPinchScalesStmt.{u} := by
  obtain ⟨U, V, W, T, Q', Q, δ₀, hgeom⟩ := exists_bufferedPinchGeometry_of_connected hT
  exact ⟨U, T, Q', Q, hgeom.toPinchPointConfiguration, fun γ α₀ ξ hγ0 hγ2 hα M hM =>
    h U V W T Q' Q δ₀ hgeom γ α₀ ξ hγ0 hγ2 hα M hM⟩

end Closure

end HarmonicBalls
