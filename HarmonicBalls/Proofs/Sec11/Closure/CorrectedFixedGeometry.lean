import HarmonicBalls.Draft.Section11Corrected
import HarmonicBalls.Proofs.Sec11.Closure.FixedGeometry

/-!
# Corrected fixed pinch-point configuration (Section 11, r7 lines 640–703)

Written argument: `notes/sec11-proof/sec11-proof-r7.tex`, paragraph "Fixed geometry" (r7 lines 640–703).
`Closure/FixedGeometry.lean` gives the sets `U, T, Q', Q`. This module adds the concentric discs
`V = B_{.02}(1.5)`, `W = B_{.04}(1.5)` and the scale `δ = 10⁻⁴`, and proves that they form an
`IsCorrectedPinchConfiguration` (`HarmonicBalls/Draft/Section11Corrected.lean`): the proof-configuration fields
of `IsPinchPointProofConfiguration` (`HarmonicBalls/Draft/Section11.lean`), the buffer fields, and the corridor
field `pinchCorridor W Q δ ⊇ {0} ∪ ∂B₅` (`Draft/Section11Corrected.lean:18`). The buffer fields are finite
distance estimates. The corridor field is a connectedness argument: the segment `[0, 5i]` and the circle `∂B₅`
form a connected subset of `B₇ \ (cl B_{2δ}(Q) ∪ cl B_{2δ}(W))` that contains `0`.
-/

namespace HarmonicBalls


open Metric Set

/-- `V = B_{.02}(1.5)` (r7 lines 640–703). -/
noncomputable def fixedV : Set ℂ := ball pinchCentreA (1 / 50)

/-- `W = B_{.04}(1.5)` (r7 lines 640–703). -/
noncomputable def fixedW : Set ℂ := ball pinchCentreA (1 / 25)

/-- The scale `δ = d = 10⁻⁴` of the written argument (r7 lines 640–703). -/
noncomputable def fixedDelta : ℝ := 1 / 10000

lemma fixedDelta_eq : fixedDelta = 1 / 10000 := rfl

/-- If every point of `A` has all its `ε`-neighbours in a closed set `K`, then `cl (thickening ε A) ⊆ K`. -/
lemma fixed_closure_thickening_subset {A K : Set ℂ} {ε : ℝ} (hK : IsClosed K)
    (h : ∀ z ∈ A, ∀ x : ℂ, dist x z < ε → x ∈ K) : closure (thickening ε A) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hx
  exact h z hz x hd

lemma fixed_isClosed_norm_ge (a : ℝ) : IsClosed {x : ℂ | a ≤ ‖x‖} :=
  isClosed_le continuous_const continuous_norm

lemma fixed_isClosed_norm_le (a : ℝ) : IsClosed {x : ℂ | ‖x‖ ≤ a} :=
  isClosed_le continuous_norm continuous_const

lemma fixed_isClosed_re_le (a : ℝ) : IsClosed {x : ℂ | x.re ≤ a} :=
  isClosed_le Complex.continuous_re continuous_const

lemma fixed_norm_bounds {x z : ℂ} {ε : ℝ} (h : dist x z < ε) :
    ‖z‖ - ε < ‖x‖ ∧ ‖x‖ < ‖z‖ + ε := by
  rw [dist_eq_norm] at h
  obtain ⟨h2, h3⟩ := abs_lt.1 (lt_of_le_of_lt (abs_norm_sub_norm_le x z) h)
  constructor <;> linarith

lemma fixed_re_bounds {x z : ℂ} {ε : ℝ} (h : dist x z < ε) :
    z.re - ε < x.re ∧ x.re < z.re + ε := by
  rw [dist_eq_norm] at h
  obtain ⟨h2, h3⟩ := abs_lt.1 (lt_of_le_of_lt (abs_re_sub_le x z) h)
  constructor <;> linarith

lemma fixed_abs_re_sub_le_dist (z w : ℂ) : |z.re - w.re| ≤ dist z w := by
  rw [dist_eq_norm]
  exact abs_re_sub_le z w

lemma fixed_abs_norm_sub_le_dist (z w : ℂ) : |‖z‖ - ‖w‖| ≤ dist z w := by
  rw [dist_eq_norm]
  exact abs_norm_sub_norm_le z w

lemma fixed_closure_U_sub : closure fixedU ⊆ closedBall pinchCentreA (1 / 100) := by
  unfold fixedU
  exact closure_ball_subset_closedBall

lemma fixed_closure_V_sub : closure fixedV ⊆ closedBall pinchCentreA (1 / 50) := by
  unfold fixedV
  exact closure_ball_subset_closedBall

lemma fixed_closure_W_sub : closure fixedW ⊆ closedBall pinchCentreA (1 / 25) := by
  unfold fixedW
  exact closure_ball_subset_closedBall

lemma fixed_closure_Q'_sub : closure fixedQ' ⊆ closedBall pinchCentreB (1 / 25) := by
  unfold fixedQ'
  exact closure_ball_subset_closedBall

lemma fixed_closure_Q_sub : closure fixedQ ⊆ closedBall pinchCentreB (1 / 10) := by
  unfold fixedQ
  exact closure_ball_subset_closedBall

lemma fixed_closure_T_F :
    closure fixedT ⊆ {z : ℂ | 7 / 5 ≤ z.re} ∪ {z : ℂ | 24 / 5 ≤ ‖z‖} :=
  closure_minimal fixedT_subset_F isClosed_fixedF

/-- Norm bounds on the closure of `T`: `7/5 ≤ |z| ≤ 5`. -/
lemma fixed_closure_T_norm {z : ℂ} (hz : z ∈ closure fixedT) : 7 / 5 ≤ ‖z‖ ∧ ‖z‖ ≤ 5 := by
  have hball : z ∈ closedBall (0 : ℂ) 5 := by
    refine closure_minimal ?_ isClosed_closedBall hz
    intro w hw
    exact mem_closedBall.2 (le_of_lt (mem_ball.1 (fixedT_subset_annulus hw).1))
  rw [mem_closedBall, dist_zero_right] at hball
  refine ⟨?_, hball⟩
  rcases fixed_closure_T_F hz with h | h
  · have h' : 7 / 5 ≤ z.re := h
    linarith [Complex.re_le_norm z]
  · have h' : 24 / 5 ≤ ‖z‖ := h
    linarith

lemma fixedV_subset_annulus : fixedV ⊆ annulus 0 1 2 := by
  intro x hx
  have hx' : dist x pinchCentreA < 1 / 50 := hx
  obtain ⟨h1, h2⟩ := fixed_norm_bounds hx'
  rw [norm_pinchCentreA] at h1 h2
  unfold annulus
  refine ⟨mem_ball.2 ?_, ?_⟩
  · rw [dist_zero_right]
    linarith
  · rw [mem_closedBall, dist_zero_right, not_le]
    linarith

lemma fixedW_subset_annulus : fixedW ⊆ annulus 0 1 2 := by
  intro x hx
  have hx' : dist x pinchCentreA < 1 / 25 := hx
  obtain ⟨h1, h2⟩ := fixed_norm_bounds hx'
  rw [norm_pinchCentreA] at h1 h2
  unfold annulus
  refine ⟨mem_ball.2 ?_, ?_⟩
  · rw [dist_zero_right]
    linarith
  · rw [mem_closedBall, dist_zero_right, not_le]
    linarith

/-- The buffer around `cl T` of radius `10δ` lies in `{6/5 ≤ |z| ≤ 51/10}`. -/
lemma fixed_buffer_T_bounds {x : ℂ}
    (hx : x ∈ closure (thickening (10 * fixedDelta) (closure fixedT))) :
    6 / 5 ≤ ‖x‖ ∧ ‖x‖ ≤ 51 / 10 := by
  have hK : closure (thickening (10 * fixedDelta) (closure fixedT)) ⊆
      {y : ℂ | 6 / 5 ≤ ‖y‖} ∩ {y : ℂ | ‖y‖ ≤ 51 / 10} := by
    refine fixed_closure_thickening_subset ((fixed_isClosed_norm_ge _).inter
      (fixed_isClosed_norm_le _)) ?_
    intro z hz y hy
    obtain ⟨h1, h2⟩ := fixed_closure_T_norm hz
    obtain ⟨h3, h4⟩ := fixed_norm_bounds hy
    constructor
    · show (6 / 5 : ℝ) ≤ ‖y‖
      linarith [fixedDelta_eq]
    · show ‖y‖ ≤ (51 / 10 : ℝ)
      linarith [fixedDelta_eq]
  exact ⟨(hK hx).1, (hK hx).2⟩

lemma fixed_buffer_T_annulus :
    closure (thickening (10 * fixedDelta) (closure fixedT)) ⊆ annulus 0 1 6 := by
  intro x hx
  obtain ⟨h1, h2⟩ := fixed_buffer_T_bounds hx
  unfold annulus
  refine ⟨mem_ball.2 ?_, ?_⟩
  · rw [dist_zero_right]
    linarith
  · rw [mem_closedBall, dist_zero_right, not_le]
    linarith

lemma fixed_buffer_U : closure (thickening (10 * fixedDelta) (closure fixedU)) ⊆ fixedV := by
  have h : closure (thickening (10 * fixedDelta) (closure fixedU)) ⊆
      closedBall pinchCentreA (11 / 1000) := by
    refine fixed_closure_thickening_subset isClosed_closedBall ?_
    intro z hz y hy
    have hz' := mem_closedBall.1 (fixed_closure_U_sub hz)
    rw [mem_closedBall]
    linarith [dist_triangle y z pinchCentreA, fixedDelta_eq]
  exact h.trans (closedBall_subset_ball (by norm_num))

lemma fixed_buffer_V : closure (thickening (10 * fixedDelta) (closure fixedV)) ⊆ fixedW := by
  have h : closure (thickening (10 * fixedDelta) (closure fixedV)) ⊆
      closedBall pinchCentreA (21 / 1000) := by
    refine fixed_closure_thickening_subset isClosed_closedBall ?_
    intro z hz y hy
    have hz' := mem_closedBall.1 (fixed_closure_V_sub hz)
    rw [mem_closedBall]
    linarith [dist_triangle y z pinchCentreA, fixedDelta_eq]
  exact h.trans (closedBall_subset_ball (by norm_num))

lemma fixed_buffer_W :
    closure (thickening (10 * fixedDelta) (closure fixedW)) ⊆ fixedT ∩ annulus 0 1 2 := by
  have h : closure (thickening (10 * fixedDelta) (closure fixedW)) ⊆
      closedBall pinchCentreA (41 / 1000) := by
    refine fixed_closure_thickening_subset isClosed_closedBall ?_
    intro z hz y hy
    have hz' := mem_closedBall.1 (fixed_closure_W_sub hz)
    rw [mem_closedBall]
    linarith [dist_triangle y z pinchCentreA, fixedDelta_eq]
  intro x hx
  have hx' := mem_closedBall.1 (h hx)
  obtain ⟨h1, h2⟩ := fixed_norm_bounds (ε := 42 / 1000)
    (lt_of_le_of_lt hx' (by norm_num))
  rw [norm_pinchCentreA] at h1 h2
  refine ⟨Or.inl (Or.inl (mem_ball.2 (lt_of_le_of_lt hx' (by norm_num)))), ?_⟩
  unfold annulus
  refine ⟨mem_ball.2 ?_, ?_⟩
  · rw [dist_zero_right]
    linarith
  · rw [mem_closedBall, dist_zero_right, not_le]
    linarith

lemma fixed_buffer_Q' : closure (thickening (10 * fixedDelta) (closure fixedQ')) ⊆ fixedQ := by
  have h : closure (thickening (10 * fixedDelta) (closure fixedQ')) ⊆
      closedBall pinchCentreB (41 / 1000) := by
    refine fixed_closure_thickening_subset isClosed_closedBall ?_
    intro z hz y hy
    have hz' := mem_closedBall.1 (fixed_closure_Q'_sub hz)
    rw [mem_closedBall]
    linarith [dist_triangle y z pinchCentreB, fixedDelta_eq]
  exact h.trans (closedBall_subset_ball (by norm_num))

lemma fixed_buffer_Q :
    closure (thickening (10 * fixedDelta) (closure fixedQ)) ⊆
      annulus 0 4 5 \ thickening (10 * fixedDelta) (closure fixedT) := by
  have hK1 : closure (thickening (10 * fixedDelta) (closure fixedQ)) ⊆
      {y : ℂ | 429 / 100 ≤ ‖y‖} ∩ {y : ℂ | ‖y‖ ≤ 451 / 100} := by
    refine fixed_closure_thickening_subset ((fixed_isClosed_norm_ge _).inter
      (fixed_isClosed_norm_le _)) ?_
    intro z hz y hy
    have hz' := mem_closedBall.1 (fixed_closure_Q_sub hz)
    obtain ⟨a1, a2⟩ := abs_le.1 (le_trans (fixed_abs_norm_sub_le_dist z pinchCentreB) hz')
    rw [norm_pinchCentreB] at a1 a2
    obtain ⟨b1, b2⟩ := fixed_norm_bounds hy
    constructor
    · show (429 / 100 : ℝ) ≤ ‖y‖
      linarith [fixedDelta_eq]
    · show ‖y‖ ≤ (451 / 100 : ℝ)
      linarith [fixedDelta_eq]
  have hK2 : closure (thickening (10 * fixedDelta) (closure fixedQ)) ⊆
      {y : ℂ | y.re ≤ -(429 / 100)} ∩ {y : ℂ | ‖y‖ ≤ 46 / 10} := by
    refine fixed_closure_thickening_subset ((fixed_isClosed_re_le _).inter
      (fixed_isClosed_norm_le _)) ?_
    intro z hz y hy
    have hz' := mem_closedBall.1 (fixed_closure_Q_sub hz)
    obtain ⟨a1, a2⟩ := abs_le.1 (le_trans (fixed_abs_re_sub_le_dist z pinchCentreB) hz')
    rw [pinchCentreB_re] at a1 a2
    obtain ⟨b1, b2⟩ := fixed_re_bounds hy
    obtain ⟨c1, c2⟩ := abs_le.1 (le_trans (fixed_abs_norm_sub_le_dist z pinchCentreB) hz')
    rw [norm_pinchCentreB] at c1 c2
    obtain ⟨d1, d2⟩ := fixed_norm_bounds hy
    constructor
    · show y.re ≤ -(429 / 100 : ℝ)
      linarith [fixedDelta_eq]
    · show ‖y‖ ≤ (46 / 10 : ℝ)
      linarith [fixedDelta_eq]
  intro x hx
  have hxn0 : 429 / 100 ≤ ‖x‖ := (hK1 hx).1
  have hxn1 : ‖x‖ ≤ 451 / 100 := (hK1 hx).2
  have hxre : x.re ≤ -(429 / 100) := (hK2 hx).1
  have hxn2 : ‖x‖ ≤ 46 / 10 := (hK2 hx).2
  refine ⟨?_, ?_⟩
  · unfold annulus
    refine ⟨mem_ball.2 ?_, ?_⟩
    · rw [dist_zero_right]
      linarith
    · rw [mem_closedBall, dist_zero_right, not_le]
      linarith
  · intro hT
    obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hT
    rcases fixed_closure_T_F hz with h | h
    · have h' : 7 / 5 ≤ z.re := h
      obtain ⟨b1, b2⟩ := fixed_re_bounds hd
      linarith [fixedDelta_eq]
    · have h' : 24 / 5 ≤ ‖z‖ := h
      obtain ⟨d1, d2⟩ := fixed_norm_bounds hd
      linarith [fixedDelta_eq]

lemma fixed_isPreconnected_segment :
    IsPreconnected ((fun t : ℝ => (t : ℂ) * Complex.I) '' Icc (0 : ℝ) 5) :=
  isPreconnected_Icc.image _ (Complex.continuous_ofReal.mul continuous_const).continuousOn

/-- The corridor field: `{0} ∪ ∂B₅ ⊆ pinchCorridor W Q δ`, the connected component of `0` in
`B₇ \ (cl B_{2δ}(Q) ∪ cl B_{2δ}(W))`. The vertical segment `[0, 5i]` and the circle `∂B₅` form a
connected subset of this region containing `0`. -/
lemma fixed_corridor_contains :
    ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchCorridor fixedW fixedQ fixedDelta := by
  unfold pinchCorridor
  have hO1 : closure (thickening (2 * fixedDelta) fixedQ) ⊆
      closedBall pinchCentreB (1 / 10 + 1 / 5000) := by
    refine fixed_closure_thickening_subset isClosed_closedBall ?_
    intro z hz y hy
    have hz' : dist z pinchCentreB < 1 / 10 := hz
    rw [mem_closedBall]
    linarith [dist_triangle y z pinchCentreB, fixedDelta_eq]
  have hO2 : closure (thickening (2 * fixedDelta) fixedW) ⊆
      closedBall pinchCentreA (1 / 25 + 1 / 5000) := by
    refine fixed_closure_thickening_subset isClosed_closedBall ?_
    intro z hz y hy
    have hz' : dist z pinchCentreA < 1 / 25 := hz
    rw [mem_closedBall]
    linarith [dist_triangle y z pinchCentreA, fixedDelta_eq]
  have hseg : ∀ t ∈ Icc (0 : ℝ) 5, ((t : ℂ) * Complex.I) ∈
      ball (0 : ℂ) 7 \ (closure (thickening (2 * fixedDelta) fixedQ) ∪
        closure (thickening (2 * fixedDelta) fixedW)) := by
    intro t ht
    have hre : ((t : ℂ) * Complex.I).re = 0 := by simp
    have hnorm : ‖(t : ℂ) * Complex.I‖ = t := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_of_nonneg ht.1]
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, hnorm]
      linarith [ht.2]
    · rintro (h | h)
      · have h1 := fixed_abs_re_sub_le_dist ((t : ℂ) * Complex.I) pinchCentreB
        rw [hre, pinchCentreB_re] at h1
        have h2 := mem_closedBall.1 (hO1 h)
        have h3 := abs_le.1 (h1.trans h2)
        linarith [h3.2, fixedDelta_eq]
      · have h1 := fixed_abs_re_sub_le_dist ((t : ℂ) * Complex.I) pinchCentreA
        rw [hre, pinchCentreA_re] at h1
        have h2 := mem_closedBall.1 (hO2 h)
        have h3 := abs_le.1 (h1.trans h2)
        linarith [h3.1, fixedDelta_eq]
  have hsph : ∀ z ∈ sphere (0 : ℂ) 5, z ∈ ball (0 : ℂ) 7 \
      (closure (thickening (2 * fixedDelta) fixedQ) ∪
        closure (thickening (2 * fixedDelta) fixedW)) := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, hz]
      norm_num
    · rintro (h | h)
      · have h1 := fixed_abs_norm_sub_le_dist z pinchCentreB
        rw [norm_pinchCentreB, hz] at h1
        have h2 := mem_closedBall.1 (hO1 h)
        have h3 := abs_le.1 (h1.trans h2)
        linarith [h3.2, fixedDelta_eq]
      · have h1 := fixed_abs_norm_sub_le_dist z pinchCentreA
        rw [norm_pinchCentreA, hz] at h1
        have h2 := mem_closedBall.1 (hO2 h)
        have h3 := abs_le.1 (h1.trans h2)
        linarith [h3.2, fixedDelta_eq]
  have hpt : ((5 : ℝ) : ℂ) * Complex.I ∈ (fun t : ℝ => (t : ℂ) * Complex.I) '' Icc (0 : ℝ) 5 :=
    ⟨5, ⟨by norm_num, le_rfl⟩, rfl⟩
  have hpt' : ((5 : ℝ) : ℂ) * Complex.I ∈ sphere (0 : ℂ) 5 := by
    rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num)]
  have hsphC : IsPreconnected (sphere (0 : ℂ) 5) :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) 0
      (by norm_num : (0 : ℝ) ≤ 5)).isPreconnected
  have hC : IsPreconnected ((fun t : ℝ => (t : ℂ) * Complex.I) '' Icc (0 : ℝ) 5 ∪
      sphere (0 : ℂ) 5) :=
    IsPreconnected.union _ hpt hpt' fixed_isPreconnected_segment hsphC
  have hCS : ((fun t : ℝ => (t : ℂ) * Complex.I) '' Icc (0 : ℝ) 5 ∪ sphere (0 : ℂ) 5) ⊆
      ball (0 : ℂ) 7 \ (closure (thickening (2 * fixedDelta) fixedQ) ∪
        closure (thickening (2 * fixedDelta) fixedW)) := by
    rintro w (⟨t, ht, rfl⟩ | hw)
    · exact hseg t ht
    · exact hsph w hw
  have h0 : (0 : ℂ) ∈ ((fun t : ℝ => (t : ℂ) * Complex.I) '' Icc (0 : ℝ) 5 ∪
      sphere (0 : ℂ) 5) :=
    Or.inl ⟨0, ⟨le_rfl, by norm_num⟩, by simp⟩
  have hsub := hC.subset_connectedComponentIn h0 hCS
  intro z hz
  rcases hz with h | h
  · rw [Set.mem_singleton_iff.1 h]
    exact hsub h0
  · exact hsub (Or.inr h)

lemma fixed_closure_U_subset_V : closure fixedU ⊆ fixedV :=
  fixed_closure_U_sub.trans (closedBall_subset_ball (by norm_num : (1 / 100 : ℝ) < 1 / 50))

lemma fixed_closure_V_subset_W : closure fixedV ⊆ fixedW :=
  fixed_closure_V_sub.trans (closedBall_subset_ball (by norm_num : (1 / 50 : ℝ) < 1 / 25))

lemma fixed_closure_W_subset_T : closure fixedW ⊆ fixedT := by
  intro x hx
  have hx' : dist x pinchCentreA ≤ 1 / 25 := mem_closedBall.1 (fixed_closure_W_sub hx)
  exact Or.inl (Or.inl (mem_ball.2 (lt_of_le_of_lt hx' (by norm_num))))

lemma fixed_concentric :
    ∃ (c : ℂ) (ρU ρV ρW : ℝ), fixedU = ball c ρU ∧ fixedV = ball c ρV ∧ fixedW = ball c ρW :=
  ⟨pinchCentreA, 1 / 100, 1 / 50, 1 / 25, rfl, rfl, rfl⟩

lemma fixed_delta_mem : fixedDelta ∈ Ioo (0 : ℝ) (1 / 100) := by
  rw [fixedDelta_eq]
  exact ⟨by norm_num, by norm_num⟩

lemma fixed_delta_small : fixedDelta < 1 / 1000 := by
  rw [fixedDelta_eq]
  norm_num

lemma fixed_thickening_mono {A B : Set ℂ} (h : A ⊆ B) (ε : ℝ) :
    thickening ε A ⊆ thickening ε B := by
  intro x hx
  obtain ⟨z, hz, hd⟩ := mem_thickening_iff.1 hx
  exact mem_thickening_iff.2 ⟨z, h hz, hd⟩

lemma fixed_closure_thickening_mono {A B : Set ℂ} (h : A ⊆ B) (ε : ℝ) :
    closure (thickening ε A) ⊆ closure (thickening ε B) :=
  closure_mono (fixed_thickening_mono h ε)

lemma fixed_thickening_T : closure (thickening (10 * fixedDelta) fixedT) ⊆ annulus 0 1 6 :=
  (fixed_closure_thickening_mono (subset_closure : fixedT ⊆ closure fixedT)
    (10 * fixedDelta)).trans fixed_buffer_T_annulus

lemma fixed_thickening_U : closure (thickening (10 * fixedDelta) fixedU) ⊆ fixedV :=
  (fixed_closure_thickening_mono (subset_closure : fixedU ⊆ closure fixedU)
    (10 * fixedDelta)).trans fixed_buffer_U

lemma fixed_thickening_V : closure (thickening (10 * fixedDelta) fixedV) ⊆ fixedW :=
  (fixed_closure_thickening_mono (subset_closure : fixedV ⊆ closure fixedV)
    (10 * fixedDelta)).trans fixed_buffer_V

lemma fixed_thickening_W : closure (thickening (10 * fixedDelta) fixedW) ⊆ annulus 0 1 2 :=
  (fixed_closure_thickening_mono (subset_closure : fixedW ⊆ closure fixedW)
    (10 * fixedDelta)).trans (fixed_buffer_W.trans Set.inter_subset_right)

lemma fixed_thickening_Q' : closure (thickening (10 * fixedDelta) fixedQ') ⊆ fixedQ :=
  (fixed_closure_thickening_mono (subset_closure : fixedQ' ⊆ closure fixedQ')
    (10 * fixedDelta)).trans fixed_buffer_Q'

lemma fixed_thickening_Q :
    closure (thickening (10 * fixedDelta) fixedQ) ⊆
      annulus 0 4 5 \ thickening (10 * fixedDelta) fixedT :=
  (fixed_closure_thickening_mono (subset_closure : fixedQ ⊆ closure fixedQ)
    (10 * fixedDelta)).trans (fixed_buffer_Q.trans (Set.sdiff_subset_sdiff_right
      (fixed_thickening_mono (subset_closure : fixedT ⊆ closure fixedT) (10 * fixedDelta))))

/-- The corrected fixed pinch-point configuration (r7 lines 640–703). -/
theorem isCorrectedPinchConfiguration_fixed :
    IsCorrectedPinchConfiguration fixedU fixedV fixedW fixedT fixedQ' fixedQ fixedDelta :=
  { toIsPinchPointProofConfiguration :=
      { toIsPinchPointConfiguration := isPinchPointConfiguration_fixed
        concentric := fixed_concentric
        closure_U_subset_V := fixed_closure_U_subset_V
        closure_V_subset_W := fixed_closure_V_subset_W
        closure_W_subset_T := fixed_closure_W_subset_T
        V_subset := fixedV_subset_annulus
        W_subset := fixedW_subset_annulus
        δ₀_mem := fixed_delta_mem
        thickening_T := fixed_thickening_T
        thickening_U := fixed_thickening_U
        thickening_V := fixed_thickening_V
        thickening_W := fixed_thickening_W
        thickening_Q' := fixed_thickening_Q'
        thickening_Q := fixed_thickening_Q }
    delta_small := fixed_delta_small
    buffer_T := fixed_buffer_T_annulus
    buffer_U := fixed_buffer_U
    buffer_V := fixed_buffer_V
    buffer_W := fixed_buffer_W
    buffer_Q' := fixed_buffer_Q'
    buffer_Q := fixed_buffer_Q
    corridor_contains := fixed_corridor_contains }

/-- Existence of a corrected pinch-point configuration. -/
theorem exists_isCorrectedPinchConfiguration :
    ∃ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsCorrectedPinchConfiguration U V W T Q' Q δ :=
  ⟨fixedU, fixedV, fixedW, fixedT, fixedQ', fixedQ, fixedDelta, isCorrectedPinchConfiguration_fixed⟩

#print axioms isCorrectedPinchConfiguration_fixed
#print axioms exists_isCorrectedPinchConfiguration

end HarmonicBalls
