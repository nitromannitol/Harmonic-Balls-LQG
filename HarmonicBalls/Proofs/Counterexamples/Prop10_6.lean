import HarmonicBalls.Draft.Section10

/-!
# Proposition 10.6 as printed is false (correction C16)

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), Proposition 10.6
(prop:boundary-simple-loop, lines 2622-2624). The printed statement reads: almost surely, for all `t > 0` and
`z ∈ B_1` with `Λ_t(z) ⋐ B_1`, each of the connected components of `B_1 \ closure Λ_t(z)` has a boundary which is a
simple loop. This file formalizes that *published* statement (`PublishedComplementComponentBoundarySimpleLoopStmt`)
and proves that it fails whenever its hypothesis holds: it is equivalent to the assertion that almost surely no
cluster `Λ_t(z)`, `t > 0`, `z ∈ B_1`, is compactly contained in `B_1`
(`publishedComplementComponentBoundarySimpleLoopStmt_iff`), i.e. the printed statement is vacuous or false. Since
`⋂_{t>0} closure Λ_t(z) = {z}` for `z ∈ B_{1/2}` (eq:contains-origin, Proposition 5.2) and the clusters increase
in `t` (Lemma A.3), small clusters are compactly contained in `B_1`, so the printed statement contradicts
Proposition 5.2. The draft
(`ComplementComponentBoundarySimpleLoopStmt`, `Draft/Section10.lean`) uses the components of `ℂ \ closure Λ_t(z)`,
as the proof (line 2628) and Proposition 10.7 do (correction C16).

## The argument (`exists_connectedComponentIn_ball_sdiff_not_isSimpleLoop`)

Let `K ⊆ B_1` be a non-empty compact set (here `K = closure Λ_t(z)`, which contains the pole `z`). Choose
`r ∈ [1/2, 1)` with `K ⊆ B_r` and let `C` be the connected component of `B_1 \ K` containing the annulus
`𝔸 = B_1 \ closedBall 0 r` (connected: the image under `exp` of the strip `{log r < Re < 0}`). Then:

* `frontier C ⊆ K ∪ ∂B_1`: a point of `B_1 \ K` in `closure C` lies in `C` (components of open subsets of `ℂ` are
  open), and `C` is open, so it is not in `frontier C`;
* `1 ∈ frontier C`, since `1 ∈ closure 𝔸`;
* `frontier C` meets `K`: otherwise `C` is closed in the connected ball `B_1`, hence equal to `B_1 ⊇ K ≠ ∅`.

So `frontier C` meets both of the disjoint open sets `B_r ⊇ K` and `ℂ \ closedBall 0 r ⊇ ∂B_1` and is covered by
them: it is disconnected, while a simple loop, the image of the connected circle `𝕋`, is connected.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Topology

universe u

/-- A simple loop (Definition 10.2, line 2553) is connected: it is the image of the connected circle `𝕋`. -/
theorem IsSimpleLoop.isConnected {Γ : Set ℂ} (h : IsSimpleLoop Γ) : IsConnected Γ := by
  obtain ⟨φ, hφ, -, rfl⟩ := h
  exact isConnected_range hφ

/-- The open annulus `𝔸_{r,1}(0) = B_1 \ closedBall 0 r`, `0 < r`, is preconnected: it is the image under the
exponential of the strip `{log r < Re < 0}`. -/
theorem isPreconnected_ball_one_sdiff_closedBall {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball (0 : ℂ) 1 \ closedBall 0 r) := by
  have hS : IsPreconnected {c : ℂ | Real.log r < c.re ∧ c.re < 0} :=
    ((convex_halfSpace_re_gt (Real.log r)).inter (convex_halfSpace_re_lt 0)).isPreconnected
  have heq : Complex.exp '' {c : ℂ | Real.log r < c.re ∧ c.re < 0} = ball (0 : ℂ) 1 \ closedBall 0 r := by
    ext w
    constructor
    · rintro ⟨c, ⟨h1, h2⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, Complex.norm_exp]
        exact Real.exp_lt_one_iff.mpr h2
      · rw [mem_closedBall, dist_zero_right, Complex.norm_exp, not_le]
        exact (Real.exp_log hr).symm.trans_lt (Real.exp_lt_exp.mpr h1)
    · rintro ⟨h1, h2⟩
      rw [mem_ball, dist_zero_right] at h1
      rw [mem_closedBall, dist_zero_right, not_le] at h2
      have hw : w ≠ 0 := by
        rintro rfl
        rw [norm_zero] at h2
        exact absurd h2 (not_lt.mpr hr.le)
      refine ⟨Complex.log w, ⟨?_, ?_⟩, Complex.exp_log hw⟩
      · rw [Complex.log_re]
        exact Real.log_lt_log hr h2
      · rw [Complex.log_re]
        exact Real.log_neg (norm_pos_iff.mpr hw) h1
  rw [← heq]
  exact hS.image _ Complex.continuous_exp.continuousOn

/-- In a locally connected space, a point of an open set `F` lying in the closure of a connected component of `F`
lies in that component (components of open sets are open). -/
theorem mem_connectedComponentIn_of_mem_closure {α : Type*} [TopologicalSpace α] [LocallyConnectedSpace α]
    {F : Set α} (hF : IsOpen F) {p x : α} (hx : x ∈ F) (hxc : x ∈ closure (connectedComponentIn F p)) :
    x ∈ connectedComponentIn F p := by
  obtain ⟨y, hyx, hyp⟩ :=
    mem_closure_iff.mp hxc _ hF.connectedComponentIn (mem_connectedComponentIn hx)
  rw [connectedComponentIn_eq hyp, ← connectedComponentIn_eq hyx]
  exact mem_connectedComponentIn hx

/-- **The printed Proposition 10.6 fails for every non-empty compact `K ⊆ B_1`.** Some connected component `C` of
`B_1 \ K` (the one containing the annulus `B_1 \ closedBall 0 r`, `K ⊆ B_r`) has a frontier which is not a simple
loop: `frontier C ⊆ K ∪ ∂B_1` meets both `K` and `∂B_1`, so it is disconnected. -/
theorem exists_connectedComponentIn_ball_sdiff_not_isSimpleLoop {K : Set ℂ} (hK : IsCompact K)
    (hKne : K.Nonempty) (hKB : K ⊆ ball 0 1) :
    ∃ C ∈ connectedComponentsIn (ball (0 : ℂ) 1 \ K), ¬ IsSimpleLoop (frontier C) := by
  obtain ⟨r₀, hr₀, hKr₀⟩ := exists_lt_subset_ball hK.isClosed hKB
  set r : ℝ := max r₀ (1 / 2) with hr_def
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hr1 : r < 1 := max_lt hr₀ (by norm_num)
  have hKr : K ⊆ ball 0 r := hKr₀.trans (ball_subset_ball (le_max_left _ _))
  set F : Set ℂ := ball (0 : ℂ) 1 \ K with hF_def
  have hFo : IsOpen F := isOpen_ball.sdiff hK.isClosed
  set A : Set ℂ := ball (0 : ℂ) 1 \ closedBall 0 r with hA_def
  have hAF : A ⊆ F := fun w hw => ⟨hw.1, fun hwK => hw.2 (ball_subset_closedBall (hKr hwK))⟩
  -- a real point of the annulus `A`
  have hrealA : ∀ s : ℝ, r < s → s < 1 → ((s : ℂ) ∈ A) := by
    intro s hs1 hs2
    have hs : ‖(s : ℂ)‖ = s := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hr0.trans hs1)]
    refine ⟨?_, ?_⟩
    · rw [mem_ball, dist_zero_right, hs]; exact hs2
    · rw [mem_closedBall, dist_zero_right, hs, not_le]; exact hs1
  set p : ℂ := (((1 + r) / 2 : ℝ) : ℂ) with hp_def
  have hpA : p ∈ A := hrealA _ (by linarith) (by linarith)
  set C : Set ℂ := connectedComponentIn F p with hC_def
  have hAC : A ⊆ C := (isPreconnected_ball_one_sdiff_closedBall hr0).subset_connectedComponentIn hpA hAF
  have hCo : IsOpen C := hFo.connectedComponentIn
  have hCF : C ⊆ F := connectedComponentIn_subset F p
  refine ⟨C, mem_image_of_mem _ (hAF hpA), fun hloop => ?_⟩
  -- `frontier C ⊆ K ∪ ∂B_1`
  have hfr : ∀ x ∈ frontier C, x ∈ K ∨ ‖x‖ = 1 := by
    intro x hx
    rw [hCo.frontier_eq] at hx
    obtain ⟨hxc, hxC⟩ := hx
    have hx1 : ‖x‖ ≤ 1 := by
      have := closure_mono (hCF.trans sdiff_subset) hxc
      rwa [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right] at this
    by_cases hxK : x ∈ K
    · exact Or.inl hxK
    · refine Or.inr (le_antisymm hx1 (not_lt.mp fun hlt => hxC ?_))
      have hxF : x ∈ F := ⟨by rwa [mem_ball, dist_zero_right], hxK⟩
      exact mem_connectedComponentIn_of_mem_closure hFo hxF hxc
  -- `1 ∈ frontier C`
  have h1fr : (1 : ℂ) ∈ frontier C := by
    rw [hCo.frontier_eq]
    refine ⟨closure_mono hAC (Metric.mem_closure_iff.mpr fun ε hε => ?_), fun h1C => ?_⟩
    · set s : ℝ := max (1 - ε / 2) ((1 + r) / 2) with hs_def
      have hs1 : r < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have hs2 : s < 1 := max_lt (by linarith) (by linarith)
      refine ⟨(s : ℂ), hrealA s hs1 hs2, ?_⟩
      rw [Complex.dist_eq, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by linarith)]
      have : 1 - ε / 2 ≤ s := le_max_left _ _
      linarith
    · have := (hCF h1C).1
      rw [mem_ball, dist_zero_right, norm_one] at this
      exact lt_irrefl _ this
  -- `frontier C` meets `K`
  have hfrK : ∃ k ∈ K, k ∈ frontier C := by
    by_contra hno
    have hsub : ball (0 : ℂ) 1 ⊆ C ∪ (closure C)ᶜ := by
      intro x hx
      by_cases hxc : x ∈ closure C
      · by_cases hxC : x ∈ C
        · exact Or.inl hxC
        · exfalso
          have hxfr : x ∈ frontier C := by rw [hCo.frontier_eq]; exact ⟨hxc, hxC⟩
          rcases hfr x hxfr with hxK | hx1
          · exact hno ⟨x, hxK, hxfr⟩
          · rw [mem_ball, dist_zero_right, hx1] at hx
            exact lt_irrefl _ hx
      · exact Or.inr hxc
    have hBC : ball (0 : ℂ) 1 ⊆ C :=
      (convex_ball (0 : ℂ) 1).isPreconnected.subset_left_of_subset_union hCo
        isClosed_closure.isOpen_compl (disjoint_compl_right.mono_left subset_closure) hsub
        ⟨p, (hAF hpA).1, mem_connectedComponentIn (hAF hpA)⟩
    obtain ⟨k, hk⟩ := hKne
    exact (hCF (hBC (hKB hk))).2 hk
  -- `frontier C` is disconnected
  obtain ⟨k, hkK, hkfr⟩ := hfrK
  have hcover : frontier C ⊆ ball (0 : ℂ) r ∪ (closedBall 0 r)ᶜ := by
    intro x hx
    rcases hfr x hx with hxK | hx1
    · exact Or.inl (hKr hxK)
    · refine Or.inr fun hxr => ?_
      rw [mem_closedBall, dist_zero_right, hx1] at hxr
      linarith
  rcases hloop.isConnected.isPreconnected.subset_or_subset isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_left ball_subset_closedBall) hcover with h | h
  · have := h h1fr
    rw [mem_ball, dist_zero_right, norm_one] at this
    linarith
  · exact h hkfr (ball_subset_closedBall (hKr hkK))

/-- The printed Proposition 10.6 fails for the cluster `Λ_t(z)` (`cluster μ 1 z t`, any measure `μ`, any `t`,
any pole `z ∈ B_1`) whenever `closure Λ_t(z) ⊆ B_1`: some connected component of `B_1 \ closure Λ_t(z)` has a
frontier which is not a simple loop. The cluster contains its pole (`self_mem_cluster`), so `closure Λ_t(z)` is a
non-empty compact subset of `B_1`. -/
theorem exists_connectedComponentIn_ball_sdiff_closure_cluster_not_isSimpleLoop (μ : Measure ℂ) {t : ℝ}
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hΛ : closure (cluster μ 1 z t) ⊆ ball 0 1) :
    ∃ C ∈ connectedComponentsIn (ball (0 : ℂ) 1 \ closure (cluster μ 1 z t)), ¬ IsSimpleLoop (frontier C) :=
  exists_connectedComponentIn_ball_sdiff_not_isSimpleLoop
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure (isBounded_ball.subset hΛ))
    ⟨z, subset_closure (self_mem_cluster hz)⟩ hΛ

/-- Proposition 10.6 (prop:boundary-simple-loop, lines 2622-2624) **as printed**: almost surely, for all `t > 0`
and `z ∈ B_1` with `Λ_t(z) ⋐ B_1`, each connected component of `B_1 \ closure Λ_t(z)` has a boundary which is a
simple loop. Random setting and objects as in `ComplementComponentBoundarySimpleLoopStmt` (`Draft/Section10.lean`),
which is the corrected statement (components of `ℂ \ closure Λ_t(z)`, correction C16). -/
def PublishedComplementComponentBoundarySimpleLoopStmt : Prop :=
  ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
    ∀ C ∈ connectedComponentsIn (ball (0 : ℂ) 1 \ closure (cluster (μ ω) 1 z t)), IsSimpleLoop (frontier C)

/-- **The printed Proposition 10.6 is vacuous or false.** It holds if and only if, almost surely, no cluster
`Λ_t(z)` with `t > 0` and `z ∈ B_1` is compactly contained in `B_1`; that is, its conclusion fails for every
`(t, z)` satisfying its hypothesis. -/
theorem publishedComplementComponentBoundarySimpleLoopStmt_iff :
    PublishedComplementComponentBoundarySimpleLoopStmt.{u} ↔
      ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
        (μ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, ¬ closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 := by
  constructor
  · intro h γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hG hL
    filter_upwards [h γ α₀ hγ hγ2 hα Ω P hC hcirc μ hG hL] with ω hω t ht z hz hΛ
    obtain ⟨C, hCc, hnot⟩ := exists_connectedComponentIn_ball_sdiff_closure_cluster_not_isSimpleLoop (μ ω) hz hΛ
    exact hnot (hω t ht z hz hΛ C hCc)
  · intro h γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hG hL
    filter_upwards [h γ α₀ hγ hγ2 hα Ω P hC hcirc μ hG hL] with ω hω t ht z hz hΛ
    exact absurd hΛ (hω t ht z hz)

end HarmonicBalls
