import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.Draft.Section11Corrected

/-!
# Section 11: connectivity consequences of [C42]

The two connectivity properties F4 and F5 follow from [C42] once `U` is nonempty;
no extra geometry field is added. Ingredients: disk-removal fact;
F4 component condition inside `B₆`; F5 connectedness of the outer piece. Proved here as derived lemmas:

* `IsBufferedPinchGeometry.zero_union_sphere_subset_six`: `{0} ∪ ∂B₅ ⊆ connectedComponentIn (B₆ \ (H_Q ∪ H_W)) 0`;
* `IsBufferedPinchGeometry.isConnected_outer_piece`: `IsConnected (T \ B_{3δ}(W))`;
* `IsBufferedPinchGeometry.corridor_contains`: the corridor containment of the corrected pinch configuration.

Notation: `H_W = closure (thickening (2δ) W)`, `H_Q = closure (thickening (2δ) Q)`, `W = ball c ρ` (`ρ > 0`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

/-- The open annulus `𝔸_{r₁,r₂}` about `0` in terms of distances. -/
lemma mem_annulus_zero {z : ℂ} {r₁ r₂ : ℝ} : z ∈ annulus (0 : ℂ) r₁ r₂ ↔ r₁ < dist z 0 ∧ dist z 0 < r₂ := by
  simp only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le]
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- Disk-removal fact. Let `G` be open and connected with `closedBall c b ⊆ G`,
and let `Q` be an upward-closed predicate on radii with `Q s` for some `s < b`, where `Q ρ` forces `ρ > 0`. Then
`{z ∈ G | Q |z - c|}` is connected. Taking `Q ρ = (a ≤ ρ)` or `Q ρ = (a < ρ)` removes an open or closed disk of
radius `a` about `c` from `G`. Proof: a point at radius `≤ s` moves radially to the circle `|z - c| = s` inside the
removed-disk complement; a point at radius `> s` follows a path in `G` until its first hit of the circle, which stays
outside the closed disk of radius `s`; the circle is connected. -/
theorem isConnected_radial_region {G : Set ℂ} (hGo : IsOpen G) (hGc : IsConnected G) {c : ℂ} {b : ℝ}
    (hb : closedBall c b ⊆ G) (Q : ℝ → Prop) (hmono : ∀ {x y : ℝ}, x ≤ y → Q x → Q y)
    (hQpos : ∀ ρ, Q ρ → 0 < ρ) {s : ℝ} (hsb : s < b) (hQs : Q s) :
    IsConnected {z : ℂ | z ∈ G ∧ Q (dist z c)} := by
  have hs0 : 0 < s := hQpos s hQs
  have hsG : ∀ z : ℂ, dist z c ≤ s → z ∈ G := fun z hz => hb (mem_closedBall.2 (hz.trans hsb.le))
  have hx0d : dist (c + (s : ℂ)) c = s := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg hs0.le]
  set X : Set ℂ := {z : ℂ | z ∈ G ∧ Q (dist z c)} with hX
  set x0 : ℂ := c + (s : ℂ) with hx0
  have hx0X : x0 ∈ X := ⟨hsG x0 hx0d.le, by rw [hx0d]; exact hQs⟩
  have hΓX : sphere c s ⊆ X := fun z hz => by
    rw [mem_sphere] at hz
    exact ⟨hsG z hz.le, by rw [hz]; exact hQs⟩
  have hΓc : IsPreconnected (sphere c s) :=
    (isConnected_sphere (by rw [Complex.rank_real_complex]; norm_num) c hs0.le).isPreconnected
  have hx0Γ : x0 ∈ sphere c s := by rw [mem_sphere]; exact hx0d
  have hΓcomp : ∀ w ∈ sphere c s, w ∈ connectedComponentIn X x0 :=
    fun w hw => hΓc.subset_connectedComponentIn hx0Γ hΓX hw
  have hstep : ∀ (A : Set ℂ) (w y : ℂ), IsPreconnected A → A ⊆ X → y ∈ A → w ∈ A → w ∈ sphere c s →
      y ∈ connectedComponentIn X x0 := by
    intro A w y hA hAX hyA hwA hwS
    have h1 : A ⊆ connectedComponentIn X w := hA.subset_connectedComponentIn hwA hAX
    have h2 : w ∈ connectedComponentIn X x0 := hΓcomp w hwS
    rw [connectedComponentIn_eq h2]
    exact h1 hyA
  have key : ∀ y ∈ X, y ∈ connectedComponentIn X x0 := by
    rintro y ⟨hyG, hyQ⟩
    have hρ0 : 0 < dist y c := hQpos _ hyQ
    rcases le_or_gt (dist y c) s with hρs | hρs
    · -- radial segment from `y` out to the circle of radius `s`
      set σ : ℝ → ℂ := fun t => c + ((((dist y c) + t * (s - dist y c)) / dist y c : ℝ) : ℂ) * (y - c) with hσ
      have hσc : Continuous σ := by
        rw [hσ]; fun_prop
      have hnorm : ∀ t ∈ Icc (0 : ℝ) 1, dist (σ t) c = dist y c + t * (s - dist y c) := by
        intro t ht
        have hk : 0 ≤ ((dist y c) + t * (s - dist y c)) / dist y c :=
          div_nonneg (by nlinarith [ht.1, ht.2]) hρ0.le
        rw [hσ, dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hk,
          ← dist_eq_norm]
        field_simp
      have hImage : σ '' Icc (0 : ℝ) 1 ⊆ X := by
        rintro _ ⟨t, ht, rfl⟩
        have hd := hnorm t ht
        have hlo : dist y c ≤ dist y c + t * (s - dist y c) := by nlinarith [ht.1]
        have hhi : dist y c + t * (s - dist y c) ≤ s := by nlinarith [ht.2]
        refine ⟨hsG _ (by rw [hd]; exact hhi), ?_⟩
        rw [hd]
        exact hmono hlo hyQ
      have hIc : IsPreconnected (σ '' Icc (0 : ℝ) 1) :=
        isPreconnected_Icc.image σ hσc.continuousOn
      have hyI : y ∈ σ '' Icc (0 : ℝ) 1 :=
        ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hσ, hρ0.ne']⟩
      have hwI : σ 1 ∈ σ '' Icc (0 : ℝ) 1 := ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
      have hw1S : σ 1 ∈ sphere c s := by
        rw [mem_sphere, hnorm 1 ⟨zero_le_one, le_rfl⟩]
        ring
      exact hstep _ (σ 1) y hIc hImage hyI hwI hw1S
    · -- the point lies outside the circle: follow a path in `G` until its first hit of the circle
      have hJ : JoinedIn G y x0 :=
        (hGo.isConnected_iff_isPathConnected.mp hGc).joinedIn y hyG x0 (hsG x0 hx0d.le)
      set φ : ℝ → ℂ := fun t => hJ.somePath (Set.projIcc (0 : ℝ) 1 zero_le_one t) with hφ
      have hφc : Continuous φ := hJ.somePath.continuous.comp continuous_projIcc
      have hφG : ∀ t, φ t ∈ G := fun t => hJ.somePath_mem _
      have hφ0 : φ 0 = y := by simp [hφ]
      have hφ1 : φ 1 = x0 := by simp [hφ]
      set A : Set ℝ := Icc (0 : ℝ) 1 ∩ {t | dist (φ t) c ≤ s} with hA
      have hAcl : IsClosed A :=
        isClosed_Icc.inter (isClosed_le (hφc.dist continuous_const) continuous_const)
      have h1A : (1 : ℝ) ∈ A := ⟨⟨zero_le_one, le_rfl⟩, by show dist (φ 1) c ≤ s; rw [hφ1, hx0d]⟩
      have hbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
      have ht1A : sInf A ∈ A := hAcl.csInf_mem ⟨1, h1A⟩ hbdd
      set t1 := sInf A with ht1def
      have ht1I : t1 ∈ Icc (0 : ℝ) 1 := ht1A.1
      have ht1le : dist (φ t1) c ≤ s := ht1A.2
      have ht1pos : 0 < t1 := by
        rcases ht1I.1.lt_or_eq with h0 | h0
        · exact h0
        · exfalso
          rw [← h0, hφ0] at ht1le
          linarith
      have hbefore : ∀ t, 0 ≤ t → t < t1 → s < dist (φ t) c := by
        intro t ht0 htt
        by_contra hcon
        rw [not_lt] at hcon
        have htA : t ∈ A := ⟨⟨ht0, by linarith [ht1I.2]⟩, hcon⟩
        exact absurd (csInf_le hbdd htA) (not_le.2 htt)
      have hatt : s ≤ dist (φ t1) c := by
        have hsub : Ico (0 : ℝ) t1 ⊆ {t | s ≤ dist (φ t) c} :=
          fun t ht => (hbefore t ht.1 ht.2).le
        have hcl : IsClosed {t : ℝ | s ≤ dist (φ t) c} :=
          isClosed_le continuous_const (hφc.dist continuous_const)
        have hmem : t1 ∈ closure (Ico (0 : ℝ) t1) := by
          rw [closure_Ico ht1pos.ne]
          exact ⟨ht1pos.le, le_rfl⟩
        exact closure_minimal hsub hcl hmem
      have hdt1 : dist (φ t1) c = s := le_antisymm ht1le hatt
      have hΦX : φ '' Icc (0 : ℝ) t1 ⊆ X := by
        rintro _ ⟨t, ht, rfl⟩
        have hst : s ≤ dist (φ t) c := by
          rcases ht.2.lt_or_eq with h | h
          · exact (hbefore t ht.1 h).le
          · rw [h, hdt1]
        exact ⟨hφG t, hmono hst hQs⟩
      have hΦc : IsPreconnected (φ '' Icc (0 : ℝ) t1) :=
        isPreconnected_Icc.image φ hφc.continuousOn
      have hyΦ : y ∈ φ '' Icc (0 : ℝ) t1 := ⟨0, ⟨le_rfl, ht1pos.le⟩, hφ0⟩
      have hwΦ : φ t1 ∈ φ '' Icc (0 : ℝ) t1 := ⟨t1, ⟨ht1pos.le, le_rfl⟩, rfl⟩
      have hwS : φ t1 ∈ sphere c s := by rw [mem_sphere]; exact hdt1
      exact hstep _ (φ t1) y hΦc hΦX hyΦ hwΦ hwS
  have hXsub : X ⊆ connectedComponentIn X x0 := fun y hy => key y hy
  have hXeq : connectedComponentIn X x0 = X :=
    Subset.antisymm (connectedComponentIn_subset X x0) hXsub
  have hconn : IsPreconnected X := by
    have := isPreconnected_connectedComponentIn (F := X) (x := x0)
    rwa [hXeq] at this
  exact ⟨⟨x0, hx0X⟩, hconn⟩

/-- The centre and radius of the faithful disk `W`, with the buffer disk `closedBall c (10δ + ρ) ⊆ T ∩ 𝔸_{1,2}`. -/
theorem IsBufferedPinchGeometry.exists_center_radius {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ (c : ℂ) (ρ : ℝ), 0 < ρ ∧ W = ball c ρ ∧ closedBall c (10 * δ + ρ) ⊆ T ∩ annulus (0 : ℂ) 1 2 := by
  obtain ⟨c, ρU, ρV, ρW, hUc, hVc, hWc⟩ := h.concentric
  obtain ⟨u, hu⟩ := h.U_nonempty
  have hδ : 0 < δ := h.delta_pos
  have hδ10 : 0 < 10 * δ := by linarith
  have huV : u ∈ V := h.buffer_U (subset_closure (self_subset_thickening hδ10 (closure U) (subset_closure hu)))
  have huW : u ∈ W := h.buffer_V (subset_closure (self_subset_thickening hδ10 (closure V) (subset_closure huV)))
  have hr : 0 < ρW := by
    have h1 := huW
    rw [hWc, mem_ball] at h1
    linarith [dist_nonneg (x := u) (y := c)]
  have hpos : 0 < 10 * δ + ρW := by linarith
  have hBW : closure (thickening (10 * δ) (closure W)) = closedBall c (10 * δ + ρW) := by
    rw [hWc, closure_ball c hr.ne', thickening_closedBall hδ10 hr.le, closure_ball _ hpos.ne']
  exact ⟨c, ρW, hr, hWc, by rw [← hBW]; exact h.buffer_W⟩

end HarmonicBalls
