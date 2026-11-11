import HarmonicBalls.FirstPass.S11j.C42Connectivity

/-!
# Section 11: F4 and F5 from [C42]

Derived lemmas, no new geometry field:

* F4 (`zero_union_sphere_subset_six`): `{0} ∪ ∂B₅ ⊆ connectedComponentIn (B₆ \ (H_Q ∪ H_W)) 0`, where
  `H_W = closure (thickening (2δ) W)` and `H_Q = closure (thickening (2δ) Q)`. Proof: the sets
  `E = B₃ \ closedBall c (2δ+ρ)` and `S = T \ closedBall c (2δ+ρ)` are connected, lie in `B₆ \ (H_Q ∪ H_W)`
  and share a point; each point of `∂B₅` is joined to `S` by a segment in a small ball of the open set.
* F5 (`isConnected_outer_piece`): `IsConnected (T \ B_{3δ}(W))`, the disk-removal fact applied to `G = T`.
* `corridor_contains`: the corridor containment `{0} ∪ ∂B₅ ⊆ pinchCorridor W Q δ` of the corrected configuration.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric

/-- F4: `{0} ∪ ∂B₅` lies in the component of `0` of
`B₆ \ (closure (B_{2δ}(Q)) ∪ closure (B_{2δ}(W)))`. -/
theorem IsBufferedPinchGeometry.zero_union_sphere_subset_six {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ({0} ∪ sphere (0 : ℂ) 5) ⊆ connectedComponentIn
      (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 := by
  obtain ⟨c, ρ, hρ, hWc, hBig⟩ := h.exists_center_radius
  have hδ : 0 < δ := h.delta_pos
  have hpos2 : 0 < 2 * δ + ρ := by linarith
  have hBT : ∀ z : ℂ, dist z c ≤ 10 * δ + ρ → z ∈ T := fun z hz => (hBig (mem_closedBall.2 hz)).1
  have hB2 : ∀ z : ℂ, dist z c ≤ 10 * δ + ρ → dist z 0 < 2 := fun z hz =>
    (mem_annulus_zero.1 (hBig (mem_closedBall.2 hz)).2).2
  have hTann : ∀ z ∈ T, dist z 0 < 5 := fun z hz => (mem_annulus_zero.1 (h.T_subset hz)).2
  have hHW : closure (thickening (2 * δ) W) = closedBall c (2 * δ + ρ) := by
    rw [hWc, thickening_ball (by linarith : (0 : ℝ) < 2 * δ) hρ, closure_ball _ hpos2.ne']
  have hHQ_sub : closure (thickening (2 * δ) Q) ⊆ closure (thickening (10 * δ) (closure Q)) := by
    apply closure_mono
    intro z hz
    obtain ⟨q, hq, hzq⟩ := mem_thickening_iff.1 hz
    exact mem_thickening_iff.2 ⟨q, subset_closure hq, lt_of_lt_of_le hzq (by linarith)⟩
  have hHQ_ann : closure (thickening (2 * δ) Q) ⊆ annulus (0 : ℂ) 4 5 :=
    fun z hz => (h.buffer_Q (hHQ_sub hz)).1
  have hHQ_T : ∀ z ∈ closure (thickening (2 * δ) Q), z ∉ T := fun z hz hzT =>
    (h.buffer_Q (hHQ_sub hz)).2
      (self_subset_thickening (by linarith : (0 : ℝ) < 10 * δ) (closure T) (subset_closure hzT))
  -- the distance from `c` to `0` and the radius bound `10δ + ρ < 2`
  have hc2 : dist c 0 < 2 := hB2 c (by rw [dist_self]; linarith)
  have hR : 10 * δ + ρ < 2 := by
    have hR0 : 0 ≤ 10 * δ + ρ := by linarith
    have hw1 : dist (c + ((10 * δ + ρ : ℝ) : ℂ)) c ≤ 10 * δ + ρ := by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hR0]
    have hw2 : dist (c - ((10 * δ + ρ : ℝ) : ℂ)) c ≤ 10 * δ + ρ := by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_of_nonneg hR0]
    have h1 := hB2 _ hw1
    have h2 := hB2 _ hw2
    have hd : dist (c + ((10 * δ + ρ : ℝ) : ℂ)) (c - ((10 * δ + ρ : ℝ) : ℂ)) = 2 * (10 * δ + ρ) := by
      rw [dist_eq_norm, show c + ((10 * δ + ρ : ℝ) : ℂ) - (c - ((10 * δ + ρ : ℝ) : ℂ))
        = ((2 * (10 * δ + ρ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    have htri := dist_triangle (c + ((10 * δ + ρ : ℝ) : ℂ)) (0 : ℂ) (c - ((10 * δ + ρ : ℝ) : ℂ))
    rw [dist_comm (0 : ℂ) (c - ((10 * δ + ρ : ℝ) : ℂ))] at htri
    linarith
  have hgap : ∀ x ∈ sphere (0 : ℂ) 5, 2 * δ + ρ < dist x c := by
    intro x hx
    have hx5 : dist x 0 = 5 := mem_sphere.1 hx
    have htri := dist_triangle x c (0 : ℂ)
    linarith
  -- the good set `G₆`
  set G6 : Set ℂ := ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)) with hG6
  have hG6open : IsOpen G6 := isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hmemG6 : ∀ z : ℂ, dist z 0 < 6 → 2 * δ + ρ < dist z c → z ∉ closure (thickening (2 * δ) Q) →
      z ∈ G6 := by
    intro z h6 hc hQ
    refine ⟨mem_ball.2 h6, fun hU => Or.elim hU hQ ?_⟩
    rw [hHW, mem_closedBall]
    intro hle
    linarith
  -- the connected sets `E` and `S`
  have hBall3 : IsConnected (ball (0 : ℂ) 3) := (convex_ball (0 : ℂ) 3).isConnected ⟨0, mem_ball_self (by norm_num)⟩
  have hb3 : closedBall c (10 * δ + ρ) ⊆ ball (0 : ℂ) 3 := fun z hz => mem_ball.2 (by linarith [hB2 z (mem_closedBall.1 hz)])
  have hEc : IsConnected {z : ℂ | z ∈ ball (0 : ℂ) 3 ∧ 2 * δ + ρ < dist z c} :=
    isConnected_radial_region isOpen_ball hBall3 hb3 (fun r' => 2 * δ + ρ < r')
      (fun hxy hx => lt_of_lt_of_le hx hxy)
      (fun r' hr' => by have : 2 * δ + ρ < r' := hr'; linarith) (s := 6 * δ + ρ) (by linarith)
      (by show 2 * δ + ρ < 6 * δ + ρ; linarith)
  have hSc : IsConnected {z : ℂ | z ∈ T ∧ 2 * δ + ρ < dist z c} :=
    isConnected_radial_region h.isOpen_T h.isConnected_T (hBig.trans inter_subset_left)
      (fun r' => 2 * δ + ρ < r') (fun hxy hx => lt_of_lt_of_le hx hxy)
      (fun r' hr' => by have : 2 * δ + ρ < r' := hr'; linarith) (s := 6 * δ + ρ) (by linarith)
      (by show 2 * δ + ρ < 6 * δ + ρ; linarith)
  have hEG6 : {z : ℂ | z ∈ ball (0 : ℂ) 3 ∧ 2 * δ + ρ < dist z c} ⊆ G6 := fun z hz =>
    hmemG6 z (lt_trans (mem_ball.1 hz.1) (by norm_num)) hz.2 (fun hQ => by
      have h4 := (hHQ_ann hQ)
      have h4' := (mem_annulus_zero.1 h4).1
      have h3 := mem_ball.1 hz.1
      linarith)
  have hSG6 : {z : ℂ | z ∈ T ∧ 2 * δ + ρ < dist z c} ⊆ G6 := fun z hz =>
    hmemG6 z (by linarith [hTann z hz.1]) hz.2 (fun hQ => hHQ_T z hQ hz.1)
  -- a point `z₀` at distance `4δ + ρ` from `c` lies in both sets
  obtain ⟨z0, hz0c⟩ : ∃ z0 : ℂ, dist z0 c = 4 * δ + ρ :=
    ⟨c + ((4 * δ + ρ : ℝ) : ℂ), by
      rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by linarith)]⟩
  have hz0T : z0 ∈ T := hBT z0 (by rw [hz0c]; linarith)
  have hz0B : dist z0 0 < 2 := hB2 z0 (by rw [hz0c]; linarith)
  have hz0E : z0 ∈ {z : ℂ | z ∈ ball (0 : ℂ) 3 ∧ 2 * δ + ρ < dist z c} :=
    ⟨mem_ball.2 (by linarith), by rw [hz0c]; linarith⟩
  have hz0S : z0 ∈ {z : ℂ | z ∈ T ∧ 2 * δ + ρ < dist z c} :=
    ⟨hz0T, by rw [hz0c]; linarith⟩
  -- the origin lies in `E`
  have h0c : 10 * δ + ρ < dist (0 : ℂ) c := by
    by_contra hcon
    rw [not_lt] at hcon
    have h2 := (mem_annulus_zero.1 (h.T_subset (hBT 0 hcon))).1
    rw [dist_self] at h2
    linarith
  have h0E : (0 : ℂ) ∈ {z : ℂ | z ∈ ball (0 : ℂ) 3 ∧ 2 * δ + ρ < dist z c} :=
    ⟨mem_ball_self (by norm_num), by linarith⟩
  have hconnES : IsPreconnected ({z : ℂ | z ∈ ball (0 : ℂ) 3 ∧ 2 * δ + ρ < dist z c} ∪
      {z : ℂ | z ∈ T ∧ 2 * δ + ρ < dist z c}) :=
    hEc.isPreconnected.union z0 hz0E hz0S hSc.isPreconnected
  have hES_G6 : ({z : ℂ | z ∈ ball (0 : ℂ) 3 ∧ 2 * δ + ρ < dist z c} ∪
      {z : ℂ | z ∈ T ∧ 2 * δ + ρ < dist z c}) ⊆ G6 := union_subset hEG6 hSG6
  have hES_comp : ({z : ℂ | z ∈ ball (0 : ℂ) 3 ∧ 2 * δ + ρ < dist z c} ∪
      {z : ℂ | z ∈ T ∧ 2 * δ + ρ < dist z c}) ⊆ connectedComponentIn G6 0 :=
    hconnES.subset_connectedComponentIn (Or.inl h0E) hES_G6
  have hS_comp : ∀ y : ℂ, y ∈ T → 2 * δ + ρ < dist y c → y ∈ connectedComponentIn G6 0 :=
    fun y hyT hyd => hES_comp (Or.inr ⟨hyT, hyd⟩)
  -- every point of `∂B₅` is joined to `S` inside a small ball of `G₆`
  rintro x (hx0 | hxS)
  · rw [Set.mem_singleton_iff.1 hx0]
    exact hES_comp (Or.inl h0E)
  · have hx5 : dist x 0 = 5 := mem_sphere.1 hxS
    have hgx := hgap x hxS
    have hxG6 : x ∈ G6 := hmemG6 x (by rw [hx5]; norm_num) hgx (fun hQ => by
      have h5 := (mem_annulus_zero.1 (hHQ_ann hQ)).2
      linarith)
    obtain ⟨ε1, hε1, hball⟩ := Metric.isOpen_iff.1 hG6open x hxG6
    have hεpos : 0 < min ε1 (dist x c - (2 * δ + ρ)) := lt_min hε1 (by linarith [hgx])
    obtain ⟨y, hyT, hxy⟩ := Metric.mem_closure_iff.1 (h.sphere_subset_closure_T hxS)
      (min ε1 (dist x c - (2 * δ + ρ))) hεpos
    have hxy2 : dist x y < dist x c - (2 * δ + ρ) := lt_of_lt_of_le hxy (min_le_right _ _)
    have hyd : 2 * δ + ρ < dist y c := by
      have htri := dist_triangle x y c
      linarith
    have hy0 : y ∈ connectedComponentIn G6 0 := hS_comp y hyT hyd
    have hballsub : ball x (min ε1 (dist x c - (2 * δ + ρ))) ⊆ G6 :=
      (ball_subset_ball (min_le_left _ _)).trans hball
    have hyball : y ∈ ball x (min ε1 (dist x c - (2 * δ + ρ))) :=
      mem_ball.2 (by rw [dist_comm]; exact hxy)
    have hxcomp : x ∈ connectedComponentIn G6 y :=
      ((convex_ball x _).isPreconnected.subset_connectedComponentIn hyball hballsub) (mem_ball_self hεpos)
    rw [connectedComponentIn_eq hy0]
    exact hxcomp

/-- F4, sphere form: `∂B₅` lies in the component of `0` of `B₆ \ (closure (B_{2δ}(Q)) ∪ closure (B_{2δ}(W)))`. -/
theorem IsBufferedPinchGeometry.sphere_subset_connectedComponentIn_six {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    sphere (0 : ℂ) 5 ⊆ connectedComponentIn
      (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 :=
  fun _ hx => h.zero_union_sphere_subset_six (Or.inr hx)

/-- F5: the outer piece `T \ B_{3δ}(W)` is connected. -/
theorem IsBufferedPinchGeometry.isConnected_outer_piece {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) : IsConnected (T \ thickening (3 * δ) W) := by
  obtain ⟨c, ρ, hρ, hWc, hBig⟩ := h.exists_center_radius
  have hδ : 0 < δ := h.delta_pos
  have h3 : (0 : ℝ) < 3 * δ := by linarith
  have hTW : thickening (3 * δ) W = ball c (3 * δ + ρ) := by
    rw [hWc, thickening_ball h3 hρ]
  have hset : T \ thickening (3 * δ) W =
      {z : ℂ | z ∈ T ∧ (fun r' : ℝ => 3 * δ + ρ ≤ r') (dist z c)} := by
    ext z
    constructor
    · rintro ⟨hzT, hzn⟩
      refine ⟨hzT, ?_⟩
      exact not_lt.1 (fun hlt => hzn (by rw [hTW]; exact mem_ball.2 hlt))
    · rintro ⟨hzT, hzd⟩
      refine ⟨hzT, fun hm => ?_⟩
      have hzd' : 3 * δ + ρ ≤ dist z c := hzd
      rw [hTW, mem_ball] at hm
      exact absurd hm (not_lt.2 hzd')
  rw [hset]
  exact isConnected_radial_region h.isOpen_T h.isConnected_T (hBig.trans inter_subset_left)
    (fun r' => 3 * δ + ρ ≤ r') (fun hxy hx => le_trans hx hxy)
    (fun r' hr' => by have : 3 * δ + ρ ≤ r' := hr'; linarith) (s := 6 * δ + ρ) (by linarith)
    (by show 3 * δ + ρ ≤ 6 * δ + ρ; linarith)

/-- The corridor containment of the corrected configuration (`Draft/Section11Corrected.lean`, `pinchCorridor`):
`{0} ∪ ∂B₅ ⊆ pinchCorridor W Q δ`, the component of `0` of `B₇ \ (closure (B_{2δ}(Q)) ∪ closure (B_{2δ}(W)))`. -/
theorem IsBufferedPinchGeometry.corridor_contains {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchCorridor W Q δ := by
  have hsub : (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) ⊆
      (ball (0 : ℂ) 7 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) :=
    fun z hz => ⟨ball_subset_ball (by norm_num) hz.1, hz.2⟩
  exact fun z hz => connectedComponentIn_mono 0 hsub (h.zero_union_sphere_subset_six hz)

end HarmonicBalls

