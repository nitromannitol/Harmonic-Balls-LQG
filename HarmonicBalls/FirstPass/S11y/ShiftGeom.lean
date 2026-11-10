import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11m.SmoothBumps

/-!
# The bump of the third shift and its geometry (Lemma 11.12, E3)

Corrected paper, lem:E3 proof (lines 3729-3755): a smooth `φ : ℂ → [0,1]` with `φ = 1` on the closure of the
set `O₂` where the internal diameter `d₂` lives, `φ = 0` near `closure U`, and support in `B_{5δ}(W)`.
Here `O₂ := thickening δ K₂` with `K₂ := closure (thickening (3δ) W \ V)`, the set of `pinchThirdEventLocal`
(FirstPass/S11h/LocalEvents.lean:51) and the domain `thickening δ K₂` of `internalDiam` (Draft/Section11.lean:89).
The support radius is `6δ` (not `5δ`), which leaves room for `closure (thickening δ K₂)` (`closure_thickening_K2_subset`).
All disjointness facts come from the buffers of `IsBufferedPinchGeometry` (FirstPass/S11h/Faithful.lean:59-64).
-/

open MeasureTheory Set Metric Filter

namespace HarmonicBalls
namespace S11y

variable {U V W T Q' Q : Set ℂ} {δ : ℝ}

/-- The set `K₂ = closure (thickening (3δ) W \ V)` of the third event (paper `K₂`). -/
abbrev pinchK2 (W V : Set ℂ) (δ : ℝ) : Set ℂ := closure (thickening (3 * δ) W \ V)

lemma isCompact_closure_of_subset_closedBall {S : Set ℂ} {R : ℝ} (hS : S ⊆ closedBall (0 : ℂ) R) :
    IsCompact (closure S) :=
  isCompact_of_isClosed_isBounded isClosed_closure
    (isBounded_closedBall.subset (closure_minimal hS isClosed_closedBall))

lemma thickening_subset_closedBall_of_subset {S : Set ℂ} {R r : ℝ} (hS : S ⊆ closedBall (0 : ℂ) R)
    (_hr : 0 ≤ r) : thickening r S ⊆ closedBall (0 : ℂ) (R + r) := by
  intro z hz
  obtain ⟨s, hs, hd⟩ := mem_thickening_iff.1 hz
  have h1 : dist s 0 ≤ R := mem_closedBall.1 (hS hs)
  have h2 : dist z 0 ≤ dist z s + dist s 0 := dist_triangle _ _ _
  exact mem_closedBall.2 (by linarith)

/-- Points of the `r`-thickening of `W ⊆ annulus 0 1 2` have norm in `(1 - r, 2 + r)`. -/
lemma norm_bounds_of_thickening {W : Set ℂ} (hW : W ⊆ annulus (0 : ℂ) 1 2) {r : ℝ} {z : ℂ}
    (hz : z ∈ thickening r W) : 1 - r < ‖z‖ ∧ ‖z‖ < 2 + r := by
  obtain ⟨w, hw, hd⟩ := mem_thickening_iff.1 hz
  have hw1 : 1 < ‖w‖ := by
    have h := (hW hw).2
    rw [mem_closedBall, dist_zero_right, not_le] at h
    exact h
  have hw2 : ‖w‖ < 2 := by
    have h := (hW hw).1
    rw [mem_ball, dist_zero_right] at h
    exact h
  have htri := abs_norm_sub_norm_le z w
  rw [← dist_eq_norm] at htri
  have hab := abs_le.1 htri
  constructor <;> linarith [hab.1, hab.2]

/-- The thickened set `thickening (6δ) W` misses the closure of `Q` (buffers of `Q` and `T`). -/
lemma not_mem_closure_Q_of_thickening (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hδ : 0 < δ)
    {z : ℂ} (hz : z ∈ thickening (6 * δ) W) : z ∉ closure Q := by
  intro hzQ
  have hzT : z ∈ thickening (10 * δ) (closure T) := by
    obtain ⟨w, hw, hd⟩ := mem_thickening_iff.1 hz
    exact mem_thickening_iff.2 ⟨w, subset_closure (hgeo.closure_W_subset_T (subset_closure hw)),
      lt_trans hd (by linarith)⟩
  have hsub : closure Q ⊆ thickening (10 * δ) (closure Q) := fun x hx =>
    mem_thickening_iff.2 ⟨x, hx, by rw [dist_self]; linarith⟩
  exact (hgeo.buffer_Q (subset_closure (hsub hzQ))).2 hzT

lemma pinchK2_disjoint_V (hV : IsOpen V) {z : ℂ} (hz : z ∈ pinchK2 W V δ) : z ∉ V := by
  have hsub : closure (thickening (3 * δ) W \ V) ⊆ Vᶜ :=
    closure_minimal (fun x hx => hx.2) hV.isClosed_compl
  exact fun hzV => hsub hz hzV

/-- `closure (thickening δ K₂) ⊆ thickening (6δ) W`. -/
lemma closure_thickening_K2_subset (hδ : 0 < δ) :
    closure (thickening δ (pinchK2 W V δ)) ⊆ thickening (6 * δ) W := by
  intro y hy
  obtain ⟨w, hw, hyw⟩ := mem_closure_iff.1 hy δ hδ
  obtain ⟨z, hzK, hwz⟩ := mem_thickening_iff.1 hw
  have hzK' : z ∈ closure (thickening (3 * δ) W \ V) := hzK
  obtain ⟨b, hb, hzb⟩ := mem_closure_iff.1 hzK' δ hδ
  obtain ⟨x, hx, hbx⟩ := mem_thickening_iff.1 hb.1
  refine mem_thickening_iff.2 ⟨x, hx, ?_⟩
  have h1 : dist y z ≤ dist y w + dist w z := dist_triangle y w z
  have h2 : dist z x ≤ dist z b + dist b x := dist_triangle z b x
  have h3 : dist y x ≤ dist y z + dist z x := dist_triangle y z x
  linarith

/-- Points of `closure (thickening δ K₂)` are at distance `> 8δ` from `closure U` (buffer of `U`). -/
lemma far_closure_U_of_K2 (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hδ : 0 < δ) :
    ∀ y ∈ closure (thickening δ (pinchK2 W V δ)), ∀ x ∈ closure U, 8 * δ ≤ dist x y := by
  intro y hy x hx
  obtain ⟨w, hw, hyw⟩ := mem_closure_iff.1 hy δ hδ
  obtain ⟨z, hzK, hwz⟩ := mem_thickening_iff.1 hw
  have hzV : z ∉ V := pinchK2_disjoint_V hgeo.isOpen_V hzK
  have h10 : 10 * δ ≤ dist x z := by
    by_contra hlt
    have hlt' : dist x z < 10 * δ := not_le.1 hlt
    have hzU : z ∈ thickening (10 * δ) (closure U) :=
      mem_thickening_iff.2 ⟨x, hx, by rw [dist_comm]; exact hlt'⟩
    exact hzV (hgeo.buffer_U (subset_closure hzU))
  have h1 : dist x z ≤ dist x y + dist y z := dist_triangle x y z
  have h2 : dist y z ≤ dist y w + dist w z := dist_triangle y w z
  linarith

/-- The third-event bump: smooth, `[0,1]`-valued, `1` on `closure (thickening δ K₂)`, `0` on `closure U`,
supported in `thickening (6δ) W`. Built as `χ · (1 - ψ)` from two smooth cutoffs. -/
theorem exists_pinchShift_bump (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ (∀ z, φ z ∈ Icc (0 : ℝ) 1) ∧
      (∀ z ∈ closure (thickening δ (pinchK2 W V δ)), φ z = 1) ∧
      (∀ z ∈ closure U, φ z = 0) ∧ (∀ z, z ∉ thickening (6 * δ) W → φ z = 0) := by
  have hδ : 0 < δ := hgeo.delta_pos
  have hWb : W ⊆ closedBall (0 : ℂ) 2 := fun z hz =>
    mem_closedBall.2 (le_of_lt (mem_ball.1 (hgeo.W_subset hz).1))
  have hUb : U ⊆ closedBall (0 : ℂ) 2 := fun z hz =>
    mem_closedBall.2 (le_of_lt (mem_ball.1 (hgeo.U_subset hz).1))
  have hK2 : pinchK2 W V δ ⊆ closedBall (0 : ℂ) (2 + 3 * δ) :=
    closure_minimal (fun z hz => thickening_subset_closedBall_of_subset hWb (by linarith) hz.1)
      isClosed_closedBall
  have hKc : IsCompact (closure (thickening δ (pinchK2 W V δ))) :=
    isCompact_closure_of_subset_closedBall
      (thickening_subset_closedBall_of_subset hK2 hδ.le)
  have hUcl : closure U ⊆ closedBall (0 : ℂ) 2 := closure_minimal hUb isClosed_closedBall
  have hUc : IsCompact (closure U) := isCompact_closure_of_subset_closedBall hUb
  obtain ⟨χ, hχs, hχc, hχ1, hχ0, hχ01⟩ :=
    exists_smooth_bump_on hKc isOpen_thickening (closure_thickening_K2_subset hδ)
      (isBounded_closedBall.subset (thickening_subset_closedBall_of_subset hWb (by linarith)))
  have hUsub : closure U ⊆ thickening (5 * δ) (closure U) := fun x hx =>
    mem_thickening_iff.2 ⟨x, hx, by rw [dist_self]; linarith⟩
  obtain ⟨ψ, hψs, hψc, hψ1, hψ0, hψ01⟩ :=
    exists_smooth_bump_on hUc isOpen_thickening hUsub
      (isBounded_closedBall.subset (thickening_subset_closedBall_of_subset hUcl (by linarith)))
  refine ⟨fun z => χ z * (1 - ψ z), hχs.mul (contDiff_const.sub hψs), hχc.mul_right, ?_, ?_, ?_, ?_⟩
  · intro z
    show χ z * (1 - ψ z) ∈ Icc (0 : ℝ) 1
    obtain ⟨h1a, h1b⟩ := hχ01 z
    obtain ⟨h2a, h2b⟩ := hψ01 z
    exact ⟨mul_nonneg h1a (by linarith), by nlinarith⟩
  · intro z hz
    show χ z * (1 - ψ z) = 1
    have hnot : z ∉ thickening (5 * δ) (closure U) := by
      intro hzU
      obtain ⟨x, hx, hd⟩ := mem_thickening_iff.1 hzU
      have hfar := far_closure_U_of_K2 hgeo hδ z hz x hx
      rw [dist_comm] at hfar
      linarith
    rw [hχ1 z hz, hψ0 z hnot]
    ring
  · intro z hz
    show χ z * (1 - ψ z) = 0
    simp [hψ1 z hz]
  · intro z hz
    show χ z * (1 - ψ z) = 0
    simp [hχ0 z hz]

end S11y
end HarmonicBalls
