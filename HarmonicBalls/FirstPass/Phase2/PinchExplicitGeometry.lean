import HarmonicBalls.FirstPass.Phase2.PinchChainedForms
import HarmonicBalls.FirstPass.Phase2.FieldAxiomsAlphaZero
import Mathlib.Analysis.Normed.Module.Connected

/-!
# An explicit buffered pinch-point geometry

The Draft statements of Lemmas 11.12 and 11.17 (`PinchEventPositiveProbabilityStmt`,
`PinchThirdEventPositiveStmt`, `Draft/Section11.lean`) quantify existentially over the configuration
`U, V, W, T, Q', Q, δ₀` of the proof of Lemma 11.12 (`IsPinchPointProofConfiguration`, lines 3237-3247), while the
corrected Lemma 11.17 (`PinchThirdEventFaithfulStmt`, `FirstPass/S11h/Faithful.lean`) holds for every fixed buffered
geometry (`IsBufferedPinchGeometry`, corrected paper lines 3157-3201). This file exhibits one configuration with both
properties:

* `U, V, W`: the open disks of radii `1/10, 2/10, 3/10` centred at `3/2`;
* `T = (𝔸_{11/10, 41/10} ∪ B_{1/2}(-9/2)) ∪ 𝔸_{49/10, 5}`: two concentric open annuli joined by a disk on the
  negative real axis (a keyhole whose hole contains `Q`);
* `Q', Q`: the open disks of radii `1/20, 1/10` centred at `9/2`;
* `δ₀ = 1/2000`.

It then derives the Draft Lemma 11.17 from the corrected one for every positive Weyl exponent `ξ` (take
`d_γ = γ / ξ`); `pinchThirdEventPositiveStmt_of_faithful` states this with the positivity of the Weyl exponent of a
γ-LQG metric as a hypothesis.
-/

namespace HarmonicBalls
namespace PinchExplicitGeometry

open MeasureTheory Set Metric

/-- The common centre `3/2` of `U, V, W`. -/
noncomputable def cU : ℂ := ((3 / 2 : ℝ) : ℂ)

/-- The common centre `9/2` of `Q', Q`. -/
noncomputable def cQ : ℂ := ((9 / 2 : ℝ) : ℂ)

/-- The centre `-9/2` of the disk joining the two annuli of `T`. -/
noncomputable def cB : ℂ := ((-9 / 2 : ℝ) : ℂ)

/-- `U = B_{1/10}(3/2)`. -/
noncomputable def gU : Set ℂ := ball cU (1 / 10)

/-- `V = B_{2/10}(3/2)`. -/
noncomputable def gV : Set ℂ := ball cU (2 / 10)

/-- `W = B_{3/10}(3/2)`. -/
noncomputable def gW : Set ℂ := ball cU (3 / 10)

/-- The keyhole `T = (𝔸_{11/10, 41/10} ∪ B_{1/2}(-9/2)) ∪ 𝔸_{49/10, 5}`. -/
noncomputable def gT : Set ℂ := (annulus 0 (11 / 10) (41 / 10) ∪ ball cB (1 / 2)) ∪ annulus 0 (49 / 10) 5

/-- `Q' = B_{1/20}(9/2)`. -/
noncomputable def gQ' : Set ℂ := ball cQ (1 / 20)

/-- `Q = B_{1/10}(9/2)`. -/
noncomputable def gQ : Set ℂ := ball cQ (1 / 10)

/-- The buffer scale `δ₀ = 1/2000`. -/
noncomputable def δ₀ : ℝ := 1 / 2000

theorem norm_ofReal_eq {a : ℝ} (ha : 0 ≤ a) : ‖((a : ℝ) : ℂ)‖ = a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]

theorem norm_cU : ‖cU‖ = 3 / 2 := norm_ofReal_eq (by norm_num)

theorem norm_cQ : ‖cQ‖ = 9 / 2 := norm_ofReal_eq (by norm_num)

theorem norm_cB : ‖cB‖ = 9 / 2 := by
  rw [cB, Complex.norm_real, Real.norm_eq_abs]; norm_num [abs_of_neg]

theorem dist_cQ_cB : dist cQ cB = 9 := by
  rw [cQ, cB, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; norm_num

theorem mem_annulus_zero {a b : ℝ} {z : ℂ} : z ∈ annulus 0 a b ↔ a < ‖z‖ ∧ ‖z‖ < b := by
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, not_le]
  exact And.comm

/-- Points of a disk have norms within the radius of the norm of the centre. -/
theorem norm_bounds_of_dist_lt {z c : ℂ} {r : ℝ} (h : dist z c < r) : ‖c‖ - r < ‖z‖ ∧ ‖z‖ < ‖c‖ + r := by
  have h1 := dist_triangle z c 0
  have h2 := dist_triangle c z 0
  simp only [dist_zero_right] at h1 h2
  rw [dist_comm] at h2
  constructor <;> linarith

/-- An open annulus centred at `0` with nonnegative inner radius is connected. -/
theorem isConnected_annulus_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : IsConnected (annulus 0 a b) := by
  let F : ℝ × ℂ → ℂ := fun p => (p.1 : ℂ) * p.2
  have hc : Continuous F := by fun_prop
  have hprod : IsConnected (Ioo a b ×ˢ sphere (0 : ℂ) 1) :=
    (isConnected_Ioo hab).prod (isConnected_sphere (by simp) 0 (by norm_num))
  have himage : F '' (Ioo a b ×ˢ sphere (0 : ℂ) 1) = annulus 0 a b := by
    ext z
    rw [mem_annulus_zero]
    constructor
    · rintro ⟨⟨t, w⟩, ⟨ht, hw⟩, rfl⟩
      have hw' : ‖w‖ = 1 := by simpa [mem_sphere, dist_zero_right] using hw
      have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
      have hn : ‖(t : ℂ) * w‖ = t := by
        rw [norm_mul, hw', mul_one]; exact norm_ofReal_eq ht0.le
      show a < ‖(t : ℂ) * w‖ ∧ ‖(t : ℂ) * w‖ < b
      rw [hn]; exact ht
    · rintro ⟨h1, h2⟩
      have hnpos : 0 < ‖z‖ := lt_of_le_of_lt ha h1
      have hne : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
      refine ⟨(‖z‖, z / (‖z‖ : ℂ)), ⟨⟨h1, h2⟩, ?_⟩, ?_⟩
      · rw [mem_sphere, dist_zero_right, norm_div, norm_ofReal_eq hnpos.le, div_self hnpos.ne']
      · show ((‖z‖ : ℝ) : ℂ) * (z / (‖z‖ : ℂ)) = z
        field_simp
  rw [← himage]
  exact hprod.image F hc.continuousOn

/-- Every point of `T` has norm in `(11/10, 5)` and distance more than `2/5` from `9/2`. -/
theorem mem_gT_bounds {y : ℂ} (hy : y ∈ gT) : 11 / 10 < ‖y‖ ∧ ‖y‖ < 5 ∧ 2 / 5 < dist y cQ := by
  have hQ := norm_cQ
  have hB := norm_cB
  have hQB := dist_cQ_cB
  have hyQ := dist_triangle cQ y 0
  simp only [dist_zero_right] at hyQ
  rw [dist_comm cQ y] at hyQ
  have hyQ' := dist_triangle y cQ 0
  simp only [dist_zero_right] at hyQ'
  rcases hy with (hy | hy) | hy
  · rw [mem_annulus_zero] at hy
    refine ⟨hy.1, by linarith [hy.2], by linarith [hy.2]⟩
  · rw [mem_ball] at hy
    have hb := norm_bounds_of_dist_lt hy
    have h3 := dist_triangle cQ y cB
    rw [dist_comm cQ y] at h3
    refine ⟨by linarith [hb.1], by linarith [hb.2], by linarith⟩
  · rw [mem_annulus_zero] at hy
    refine ⟨by linarith [hy.1], hy.2, by linarith [hy.1]⟩

theorem isOpen_gT : IsOpen gT := by
  have hA : ∀ a b : ℝ, IsOpen (annulus (0 : ℂ) a b) := fun a b => isOpen_ball.sdiff isClosed_closedBall
  exact ((hA _ _).union isOpen_ball).union (hA _ _)

theorem isConnected_gT : IsConnected gT := by
  have hA1 : IsConnected (annulus (0 : ℂ) (11 / 10) (41 / 10)) := isConnected_annulus_zero (by norm_num) (by norm_num)
  have hA2 : IsConnected (annulus (0 : ℂ) (49 / 10) 5) := isConnected_annulus_zero (by norm_num) (by norm_num)
  have hB : IsConnected (ball cB (1 / 2)) := (convex_ball _ _).isConnected (nonempty_ball.2 (by norm_num))
  have hz1 : (((-81 / 20 : ℝ) : ℂ)) ∈ annulus (0 : ℂ) (11 / 10) (41 / 10) ∩ ball cB (1 / 2) := by
    refine ⟨?_, ?_⟩
    · rw [mem_annulus_zero, Complex.norm_real, Real.norm_eq_abs]; norm_num [abs_of_neg]
    · rw [mem_ball, cB, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; norm_num
  have hz2 : (((-99 / 20 : ℝ) : ℂ)) ∈ (annulus (0 : ℂ) (11 / 10) (41 / 10) ∪ ball cB (1 / 2)) ∩
      annulus (0 : ℂ) (49 / 10) 5 := by
    refine ⟨Or.inr ?_, ?_⟩
    · rw [mem_ball, cB, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; norm_num
    · rw [mem_annulus_zero, Complex.norm_real, Real.norm_eq_abs]; norm_num [abs_of_neg]
  exact (hA1.union ⟨_, hz1⟩ hB).union ⟨_, hz2⟩ hA2

/-- A point of the closure of a `10 δ₀`-thickening is within `1/100` of the set. -/
theorem exists_dist_lt_of_mem_closure_thickening {s : Set ℂ} {x : ℂ}
    (hx : x ∈ closure (thickening (10 * δ₀) s)) : ∃ y ∈ s, dist x y < 1 / 100 := by
  obtain ⟨x', hx', hxx'⟩ := Metric.mem_closure_iff.1 hx (1 / 200) (by norm_num)
  obtain ⟨y, hy, hx'y⟩ := Metric.mem_thickening_iff.1 hx'
  refine ⟨y, hy, ?_⟩
  have h10 : 10 * δ₀ = 1 / 200 := by norm_num [δ₀]
  rw [h10] at hx'y
  linarith [dist_triangle x x' y]

theorem exists_dist_lt_of_mem_thickening {s : Set ℂ} {x : ℂ}
    (hx : x ∈ thickening (10 * δ₀) s) : ∃ y ∈ s, dist x y < 1 / 100 :=
  exists_dist_lt_of_mem_closure_thickening (subset_closure hx)

theorem exists_dist_lt_of_mem_closure {s : Set ℂ} {x : ℂ} (hx : x ∈ closure s) : ∃ y ∈ s, dist x y < 1 / 100 :=
  Metric.mem_closure_iff.1 hx (1 / 100) (by norm_num)

theorem closure_thickening_subset_ball {s : Set ℂ} {c : ℂ} {r R : ℝ} (hs : s ⊆ ball c r) (h : r + 1 / 100 ≤ R) :
    closure (thickening (10 * δ₀) s) ⊆ ball c R := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_mem_closure_thickening hx
  have hy' := hs hy
  rw [mem_ball] at hy' ⊢
  linarith [dist_triangle x y c]

theorem closure_thickening_subset_annulus {s : Set ℂ} {a b : ℝ}
    (hs : ∀ y ∈ s, a + 1 / 100 ≤ ‖y‖ ∧ ‖y‖ + 1 / 100 ≤ b) :
    closure (thickening (10 * δ₀) s) ⊆ annulus 0 a b := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_mem_closure_thickening hx
  have hb := norm_bounds_of_dist_lt (show dist y x < 1 / 100 by rwa [dist_comm])
  rw [mem_annulus_zero]
  constructor <;> linarith [hs y hy]

/-- Points of the closure or of the `10 δ₀`-thickening of `T` are at distance more than `3/10` from `9/2`. -/
theorem dist_cQ_of_near_gT {x y : ℂ} (hy : y ∈ gT) (hxy : dist x y < 1 / 100) : 3 / 10 < dist x cQ := by
  have := (mem_gT_bounds hy).2.2
  linarith [dist_triangle y x cQ, dist_comm x y]

theorem closure_gW_subset : closure gW ⊆ annulus 0 (11 / 10) (41 / 10) := by
  rw [gW, closure_ball _ (by norm_num)]
  intro x hx
  rw [mem_closedBall] at hx
  have hb := norm_bounds_of_dist_lt (show dist x cU < 31 / 100 by linarith)
  rw [norm_cU] at hb
  rw [mem_annulus_zero]
  constructor <;> linarith [hb.1, hb.2]

theorem closure_gW_subset_gT : closure gW ⊆ gT :=
  closure_gW_subset.trans (subset_union_left.trans subset_union_left)

theorem ball_cU_subset_annulus {r : ℝ} (hr : r ≤ 3 / 10) : ball cU r ⊆ annulus 0 1 2 := by
  intro x hx
  have hb := norm_bounds_of_dist_lt (mem_ball.1 hx)
  rw [norm_cU] at hb
  rw [mem_annulus_zero]
  constructor <;> linarith [hb.1, hb.2]

theorem gT_subset : gT ⊆ annulus 0 1 5 := by
  intro y hy
  have := mem_gT_bounds hy
  rw [mem_annulus_zero]
  exact ⟨by linarith [this.1], this.2.1⟩

theorem closure_gT_subset : closure gT ⊆ annulus 0 1 6 := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_mem_closure hx
  have hb := norm_bounds_of_dist_lt (show dist y x < 1 / 100 by rwa [dist_comm])
  have := mem_gT_bounds hy
  rw [mem_annulus_zero]
  constructor <;> linarith [this.1, this.2.1]

theorem closure_thickening_gT_subset : closure (thickening (10 * δ₀) gT) ⊆ annulus 0 1 6 :=
  closure_thickening_subset_annulus fun y hy => by
    have := mem_gT_bounds hy
    constructor <;> linarith [this.1, this.2.1]

theorem sphere_subset_frontier_gT : sphere (0 : ℂ) 5 ⊆ frontier gT := by
  intro z hz
  rw [mem_sphere, dist_zero_right] at hz
  rw [isOpen_gT.frontier_eq]
  refine ⟨?_, fun h => by linarith [(mem_gT_bounds h).2.1]⟩
  rw [Metric.mem_closure_iff]
  intro ε hε
  set t : ℝ := min (ε / 10) (1 / 100) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t ≤ 1 / 100 := min_le_right _ _
  have ht2 : t ≤ ε / 10 := min_le_left _ _
  refine ⟨((1 - t : ℝ) : ℂ) * z, Or.inr ?_, ?_⟩
  · rw [mem_annulus_zero, norm_mul, norm_ofReal_eq (by linarith), hz]
    constructor <;> nlinarith
  · have : z - ((1 - t : ℝ) : ℂ) * z = (t : ℂ) * z := by push_cast; ring
    rw [dist_eq_norm, this, norm_mul, norm_ofReal_eq ht0.le, hz]
    linarith

theorem gQ_subset : gQ ⊆ annulus 0 4 5 \ closure gT := by
  intro x hx
  rw [gQ, mem_ball] at hx
  have hb := norm_bounds_of_dist_lt hx
  rw [norm_cQ] at hb
  refine ⟨mem_annulus_zero.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩, fun h => ?_⟩
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_mem_closure h
  linarith [dist_cQ_of_near_gT hy hxy]

theorem closure_ball_subset_ball' {c : ℂ} {r R : ℝ} (hr : 0 < r) (h : r < R) : closure (ball c r) ⊆ ball c R := by
  rw [closure_ball _ hr.ne']; exact closedBall_subset_ball h

theorem closure_thickening_gW_subset {a b : ℝ} (ha : a + 1 / 100 ≤ 6 / 5) (hb : 9 / 5 + 1 / 100 ≤ b) :
    closure (thickening (10 * δ₀) gW) ⊆ annulus 0 a b :=
  closure_thickening_subset_annulus fun y hy => by
    have h := norm_bounds_of_dist_lt (mem_ball.1 hy)
    rw [norm_cU] at h
    constructor <;> linarith [h.1, h.2]

theorem closure_thickening_gQ_subset :
    closure (thickening (10 * δ₀) gQ) ⊆ annulus 0 4 5 \ thickening (10 * δ₀) gT := by
  intro x hx
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_mem_closure_thickening hx
  rw [gQ, mem_ball] at hy
  have hxQ : dist x cQ < 11 / 100 := by linarith [dist_triangle x y cQ]
  have hb := norm_bounds_of_dist_lt hxQ
  rw [norm_cQ] at hb
  refine ⟨mem_annulus_zero.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩, fun h => ?_⟩
  obtain ⟨t, ht, hxt⟩ := exists_dist_lt_of_mem_thickening h
  linarith [dist_cQ_of_near_gT ht hxt]

theorem closure_gQ_subset : closure gQ ⊆ annulus 0 4 5 \ closure gT := by
  intro x hx
  rw [gQ, closure_ball _ (by norm_num), mem_closedBall] at hx
  have hb := norm_bounds_of_dist_lt (show dist x cQ < 11 / 100 by linarith)
  rw [norm_cQ] at hb
  refine ⟨mem_annulus_zero.2 ⟨by linarith [hb.1], by linarith [hb.2]⟩, fun h => ?_⟩
  obtain ⟨y, hy, hxy⟩ := exists_dist_lt_of_mem_closure h
  linarith [dist_cQ_of_near_gT hy hxy]

theorem isConnected_ball' (c : ℂ) {r : ℝ} (hr : 0 < r) : IsConnected (ball c r) :=
  (convex_ball _ _).isConnected (nonempty_ball.2 hr)

/-- The explicit configuration is a configuration of the proof of Lemma 11.12 (Draft form). -/
theorem isPinchPointProofConfiguration : IsPinchPointProofConfiguration gU gV gW gT gQ' gQ δ₀ where
  isOpen_U := isOpen_ball
  isConnected_U := isConnected_ball' _ (by norm_num)
  isOpen_T := isOpen_gT
  isConnected_T := isConnected_gT
  isOpen_Q' := isOpen_ball
  isConnected_Q' := isConnected_ball' _ (by norm_num)
  isOpen_Q := isOpen_ball
  isConnected_Q := isConnected_ball' _ (by norm_num)
  closure_U_subset := (closure_mono (ball_subset_ball (by norm_num))).trans closure_gW_subset_gT
  closure_Q'_subset := closure_ball_subset_ball' (by norm_num) (by norm_num)
  exists_eq_ball := ⟨cU, 1 / 10, rfl⟩
  U_subset := ball_cU_subset_annulus (by norm_num)
  Q_subset := gQ_subset
  T_subset := gT_subset
  sphere_subset_frontier := sphere_subset_frontier_gT
  concentric := ⟨cU, 1 / 10, 2 / 10, 3 / 10, rfl, rfl, rfl⟩
  closure_U_subset_V := closure_ball_subset_ball' (by norm_num) (by norm_num)
  closure_V_subset_W := closure_ball_subset_ball' (by norm_num) (by norm_num)
  closure_W_subset_T := closure_gW_subset_gT
  V_subset := ball_cU_subset_annulus (by norm_num)
  W_subset := ball_cU_subset_annulus (by norm_num)
  δ₀_mem := ⟨by norm_num [δ₀], by norm_num [δ₀]⟩
  thickening_T := closure_thickening_gT_subset
  thickening_U := closure_thickening_subset_ball (c := cU) (r := 1 / 10) subset_rfl (by norm_num)
  thickening_V := closure_thickening_subset_ball (c := cU) (r := 2 / 10) subset_rfl (by norm_num)
  thickening_W := closure_thickening_gW_subset (by norm_num) (by norm_num)
  thickening_Q' := closure_thickening_subset_ball (c := cQ) (r := 1 / 20) subset_rfl (by norm_num)
  thickening_Q := closure_thickening_gQ_subset

/-- The explicit configuration is a buffered pinch geometry (corrected form, `[C42]`). -/
theorem isBufferedPinchGeometry : IsBufferedPinchGeometry gU gV gW gT gQ' gQ δ₀ where
  isOpen_U := isOpen_ball
  isOpen_V := isOpen_ball
  isOpen_W := isOpen_ball
  isOpen_T := isOpen_gT
  isOpen_Q' := isOpen_ball
  isOpen_Q := isOpen_ball
  isConnected_T := isConnected_gT
  isConnected_Q' := isConnected_ball' _ (by norm_num)
  isConnected_Q := isConnected_ball' _ (by norm_num)
  concentric := ⟨cU, 1 / 10, 2 / 10, 3 / 10, rfl, rfl, rfl⟩
  U_nonempty := nonempty_ball.2 (by norm_num)
  U_subset := ball_cU_subset_annulus (by norm_num)
  V_subset := ball_cU_subset_annulus (by norm_num)
  W_subset := ball_cU_subset_annulus (by norm_num)
  closure_W_subset_T := closure_gW_subset_gT
  T_subset := gT_subset
  closure_T_subset := closure_gT_subset
  sphere_subset_closure_T := sphere_subset_frontier_gT.trans frontier_subset_closure
  closure_Q'_subset_Q := closure_ball_subset_ball' (by norm_num) (by norm_num)
  closure_Q_subset := closure_gQ_subset
  delta_pos := by norm_num [δ₀]
  delta_lt := by norm_num [δ₀]
  buffer_T := by rw [thickening_closure]; exact closure_thickening_gT_subset
  buffer_U := by
    rw [thickening_closure]
    exact closure_thickening_subset_ball (c := cU) (r := 1 / 10) subset_rfl (by norm_num)
  buffer_V := by
    rw [thickening_closure]
    exact closure_thickening_subset_ball (c := cU) (r := 2 / 10) subset_rfl (by norm_num)
  buffer_W := by
    rw [thickening_closure]
    exact subset_inter ((closure_thickening_gW_subset (a := 11 / 10) (b := 41 / 10) (by norm_num)
      (by norm_num)).trans (subset_union_left.trans subset_union_left))
      (closure_thickening_gW_subset (by norm_num) (by norm_num))
  buffer_Q' := by
    rw [thickening_closure]
    exact closure_thickening_subset_ball (c := cQ) (r := 1 / 20) subset_rfl (by norm_num)
  buffer_Q := by rw [thickening_closure, thickening_closure]; exact closure_thickening_gQ_subset

end PinchExplicitGeometry

universe u

/-- A configuration of the proof of Lemma 11.12 (Draft form) that is also a buffered pinch geometry (corrected
form): the explicit keyhole configuration of `PinchExplicitGeometry`. -/
theorem exists_pinchPointProofConfiguration_bufferedPinchGeometry :
    ∃ (U V W T Q' Q : Set ℂ) (δ : ℝ), IsPinchPointProofConfiguration U V W T Q' Q δ ∧
      IsBufferedPinchGeometry U V W T Q' Q δ :=
  ⟨_, _, _, _, _, _, _, PinchExplicitGeometry.isPinchPointProofConfiguration,
    PinchExplicitGeometry.isBufferedPinchGeometry⟩

/-- Lemma 11.17 in the Draft form (`PinchThirdEventPositiveStmt`, one configuration, `α₀ = 0`, every Weyl exponent
`ξ`) from the corrected Lemma 11.17 (`PinchThirdEventFaithfulStmt`, every buffered geometry, `ξ = γ / d_γ`), given
that the Weyl exponent of a γ-LQG metric is positive (`hξ`; then `d_γ = γ / ξ`). -/
theorem pinchThirdEventPositiveStmt_of_faithful (h17 : PinchThirdEventFaithfulStmt.{u})
    (hξ : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 → 0 < ξ) :
    PinchThirdEventPositiveStmt.{u} := by
  obtain ⟨U, V, W, T, Q', Q, δ, hcfg, hbuf⟩ := exists_pinchPointProofConfiguration_bufferedPinchGeometry
  refine ⟨U, V, W, T, Q', Q, δ, hcfg, ?_⟩
  intro γ ξ hγ0 hγ2 Ω _ P hC hcirc μ D hG hμ hD M hM
  have hξ0 : 0 < ξ := by
    obtain ⟨𝔇, h𝔇, -⟩ := hD
    exact hξ γ ξ 𝔇 hγ0 hγ2 h𝔇
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  have hdiv : γ / (γ / ξ) = ξ := by field_simp
  exact h17 U V W T Q' Q δ hbuf γ 0 (γ / ξ) hγ0 hγ2 hQ (div_pos hγ0 hξ0) Ω P hC hcirc μ D hG hμ
    (by rwa [hdiv]) M hM

/-- Lemma 11.12 (Draft form) from the metric inputs of the corrected Lemma 11.17 (`hDC hFin hAx`, all literature
inputs of the LQG metric) and the positivity of the Weyl exponent (`hξ`). -/
theorem firstPass_11_12_derivedInputsMetricOfXiPos (hDC : DyadicCellDiamSmallFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hξ : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 → IsLQGMetric γ ξ 𝔇 → 0 < ξ) :
    PinchEventPositiveProbabilityStmt.{u} :=
  firstPass_11_12_derivedInputsAlphaZero
    (pinchThirdEventPositiveStmt_of_faithful (firstPass_11_17_corrected_derivedInputsMetric hDC hFin hAx) hξ)

end HarmonicBalls
