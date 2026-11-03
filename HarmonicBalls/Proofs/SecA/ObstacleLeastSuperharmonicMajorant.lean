import HarmonicBalls.Steps.SecA.ObstacleLeastSuperharmonicMajorant
import HarmonicBalls.Steps.Sec2.GreenFunctionBall
import HarmonicBalls.Proofs.Potential.DiscPoisson
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder
import HarmonicBalls.Proofs.SecA.Basic

/-!
# Lemma A.1 (lemma:appendix-basic-properties, line 3589): proofs of the steps

Proofs of the four leaves of `HarmonicBalls/Steps/SecA/ObstacleLeastSuperharmonicMajorant.lean` (Appendix A of the
corrected draft of Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity*, arXiv:2208.11795). The
admissible class is `superharmonicMajorants μ R z t` (`F`), its pointwise infimum is `lscLeastMajorant μ R z t`
(`f_t`), and `β_t = obstacle μ R z t`.

The `_of` theorems take Prop 2.3 (`GreenFunctionBallStmt`), the continuity of `q_{B_R}`
(`GreenPotentialBallContinuousStep`) and, for the pole, `ObstacleTendstoAtBotStep` as hypotheses; the `_holds`
theorems discharge them with `greenFunctionBall` (Steps/Sec2/GreenFunctionBall.lean), `greenPotentialBall_continuousOn`
(Proofs/Potential/GreenPotentialHolder.lean) and `obstacleTendstoAtBotStep_holds` (Proofs/SecA/Basic.lean).

## Main results

* `isSuperharmonicOn_lscRegularization` (AG01 Thm 3.7.5, finite-valued form): the lower semicontinuous
  regularization of the infimum of a family of superharmonic functions bounded below by `0` is superharmonic.
* `isSuperharmonicOn_poissonModification`: the Poisson modification of a superharmonic function on a disc is
  superharmonic and lies below it (lines 3634-3640, eq:superharmonic-poisson-inequality).
* `obstacleLeastSuperharmonicMajorantStep1_holds`: Step 1, minimum principle on `B_R`.
* `obstacleLeastSuperharmonicMajorantStep2_holds`: Step 2, `f_t` equals its lower semicontinuous regularization on
  `B_R`, which is an admissible majorant.
* `obstacleLeastSuperharmonicMajorantStep3_holds`: Step 3 off the pole (Poisson modification of `ε + f_t`).
* `obstacleLeastSuperharmonicMajorantStep4_holds`: Step 3 at the pole, repair of gap G2 (level `L = ε`, since
  `β_t → -∞` at the pole and `f_t ≥ 0`).
* `greenPotentialBallContinuousStep_holds`, and `obstacleLeastSuperharmonicMajorantGeneral_of_laplacian`: Lemma A.1
  (general radius and pole) given only `GreenPotentialBallLaplacianStep`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set

/-! ## Superharmonic functions: congruence and the local super-mean-value property -/

/-- Superharmonicity on `U` only depends on the values on `U`. -/
theorem IsSuperharmonicOn.congr {U : Set ℂ} {g g' : ℂ → ℝ} (h : IsSuperharmonicOn U g)
    (heq : EqOn g g' U) : IsSuperharmonicOn U g' := by
  refine ⟨fun x hx a ha => ?_, fun x hx r hr hsub => ?_⟩
  · have ha' : a < g x := by
      have ha'' : a < g' x := ha
      rwa [← heq hx] at ha''
    show ∀ᶠ y in 𝓝[U] x, a < g' y
    filter_upwards [h.1 x hx a ha', self_mem_nhdsWithin] with y hy hyU
    rwa [← heq hyU]
  · have hsph : EqOn g g' (sphere x |r|) := fun y hy =>
      heq (hsub (sphere_subset_closedBall (by rwa [abs_of_pos hr] at hy)))
    obtain ⟨h1, h2⟩ := h.2 x hx r hr hsub
    refine ⟨(circleIntegrable_congr hsph).1 h1, ?_⟩
    rw [← Real.circleAverage_congr_sphere hsph, ← heq hx]
    exact h2

/-- A superharmonic function on an open set has the local super-mean-value property. -/
theorem IsSuperharmonicOn.localSuperMean {U : Set ℂ} (hU : IsOpen U) {g : ℂ → ℝ}
    (h : IsSuperharmonicOn U g) :
    ∀ x ∈ U, ∃ ρ > 0, ∀ r ∈ Ioo 0 ρ, CircleIntegrable g x r ∧ Real.circleAverage g x r ≤ g x := by
  intro x hx
  obtain ⟨ρ, hρ, hsub⟩ := Metric.isOpen_iff.1 hU x hx
  exact ⟨ρ, hρ, fun r hr => h.2 x hx r hr.1 ((closedBall_subset_ball hr.2).trans hsub)⟩

/-- The zero function is superharmonic. -/
theorem isSuperharmonicOn_zero (U : Set ℂ) : IsSuperharmonicOn U (fun _ => (0 : ℝ)) :=
  ⟨lowerSemicontinuousOn_const, fun _ _ _ _ _ =>
    ⟨continuousOn_const.circleIntegrable', by rw [Real.circleAverage_const]⟩⟩

/-- Adding a constant preserves superharmonicity. -/
theorem IsSuperharmonicOn.const_add {U : Set ℂ} {g : ℂ → ℝ} (h : IsSuperharmonicOn U g) (a : ℝ) :
    IsSuperharmonicOn U (fun y => a + g y) := by
  refine ⟨continuousOn_const.lowerSemicontinuousOn.add h.1, fun x hx r hr hsub => ?_⟩
  obtain ⟨hi, hm⟩ := h.2 x hx r hr hsub
  have hc : CircleIntegrable (fun _ : ℂ => a) x r := continuousOn_const.circleIntegrable'
  refine ⟨hc.add hi, ?_⟩
  rw [Real.circleAverage_fun_add hc hi, Real.circleAverage_const]
  linarith

/-! ## The Poisson modification (AG01 §3.3; lines 3634-3640) -/

open Classical in
/-- The **Poisson modification** of `u` on the disc `B_ρ(c)`: the Poisson integral `P_{B_ρ(c)}[u]` in `B_ρ(c)` and
`u` elsewhere (the function `g` of lines 3634-3640). -/
noncomputable def poissonModification (u : ℂ → ℝ) (c : ℂ) (ρ : ℝ) (y : ℂ) : ℝ :=
  if y ∈ ball c ρ then discPoissonIntegral u c ρ y else u y

theorem poissonModification_of_mem {u : ℂ → ℝ} {c y : ℂ} {ρ : ℝ} (hy : y ∈ ball c ρ) :
    poissonModification u c ρ y = discPoissonIntegral u c ρ y := by
  simp [poissonModification, hy]

theorem poissonModification_of_notMem {u : ℂ → ℝ} {c y : ℂ} {ρ : ℝ} (hy : y ∉ ball c ρ) :
    poissonModification u c ρ y = u y := by
  simp [poissonModification, hy]

/-- **The Poisson modification of a superharmonic function is superharmonic** (AG01 Lemma 3.3.? / the claim
"`g` is superharmonic in `B_1`", lines 3638-3640), and it lies below `u`
(eq:superharmonic-poisson-inequality). Lower semicontinuity at `∂B_ρ(c)` follows from the lower boundary limits of
`P[u]`; the local super-mean-value property holds in `B_ρ(c)` (mean value property of `P[u]`) and off `B_ρ(c)`
(`P[u] ≤ u`); it is global by `circleAverage_le_of_localSuperMean`. -/
theorem isSuperharmonicOn_poissonModification {U : Set ℂ} (hU : IsOpen U) {u : ℂ → ℝ}
    (hu : IsSuperharmonicOn U u) {c : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hsub : closedBall c ρ ⊆ U) :
    IsSuperharmonicOn U (poissonModification u c ρ) ∧ ∀ y, poissonModification u c ρ y ≤ u y := by
  have hcU : c ∈ U := hsub (mem_closedBall_self hρ.le)
  have hui : CircleIntegrable u c ρ := (hu.2 c hcU ρ hρ hsub).1
  have hloc := hu.localSuperMean hU
  have hPle := discPoissonIntegral_le hu.1 hloc hρ hsub hui
  have hPc := continuousOn_discPoissonIntegral hui
  have hsphU : sphere c ρ ⊆ U := sphere_subset_closedBall.trans hsub
  set g := poissonModification u c ρ with hgdef
  have hgmem : ∀ y ∈ ball c ρ, g y = discPoissonIntegral u c ρ y := fun y hy => poissonModification_of_mem hy
  have hgnot : ∀ y, y ∉ ball c ρ → g y = u y := fun y hy => poissonModification_of_notMem hy
  have hgle : ∀ y, g y ≤ u y := fun y => by
    by_cases hy : y ∈ ball c ρ
    · rw [hgmem _ hy]; exact hPle y hy
    · rw [hgnot _ hy]
  have hlsc : LowerSemicontinuousOn g U := by
    intro y hy a ha
    have ha' : a < g y := ha
    show ∀ᶠ w in 𝓝[U] y, a < g w
    by_cases hyb : y ∈ ball c ρ
    · rw [hgmem _ hyb] at ha'
      have hcont : ContinuousAt (discPoissonIntegral u c ρ) y :=
        hPc.continuousAt (isOpen_ball.mem_nhds hyb)
      refine nhdsWithin_le_nhds ?_
      filter_upwards [hcont.eventually (lt_mem_nhds ha'), isOpen_ball.mem_nhds hyb] with w hw hwb
      rw [hgmem _ hwb]; exact hw
    · rw [hgnot _ hyb] at ha'
      by_cases hyc : y ∈ closedBall c ρ
      · have hys : y ∈ sphere c ρ := by rw [← closedBall_sdiff_ball]; exact ⟨hyc, hyb⟩
        have e1 := eventually_lt_discPoissonIntegral hu.1 hρ hsphU hui hys ha'
        rw [eventually_nhdsWithin_iff] at e1
        filter_upwards [nhdsWithin_le_nhds e1, hu.1 y hy a ha'] with w hw1 hw2
        by_cases hwb : w ∈ ball c ρ
        · rw [hgmem _ hwb]; exact hw1 hwb
        · rw [hgnot _ hwb]; exact hw2
      · have hopen : (closedBall c ρ)ᶜ ∈ 𝓝 y := isClosed_closedBall.isOpen_compl.mem_nhds hyc
        filter_upwards [hu.1 y hy a ha', nhdsWithin_le_nhds hopen] with w hw hwc
        have hwb : w ∉ ball c ρ := fun h => hwc (ball_subset_closedBall h)
        rw [hgnot _ hwb]; exact hw
  have hint : ∀ x r, 0 < r → closedBall x r ⊆ U → CircleIntegrable g x r := by
    intro x r hr hsubx
    have hsph : sphere x |r| ⊆ U := by rw [abs_of_pos hr]; exact sphere_subset_closedBall.trans hsubx
    obtain ⟨w, -, hwmin⟩ := (hlsc.mono hsph).exists_isMinOn
      (NormedSpace.sphere_nonempty.2 (abs_nonneg r)) (isCompact_sphere x |r|)
    exact LowerSemicontinuousOn.circleIntegrable_of_le hlsc hsph (fun y hy => hwmin hy) (fun y _ => hgle y)
      (hu.2 x (hsubx (mem_closedBall_self hr.le)) r hr hsubx).1
  have hloc' : ∀ x ∈ U, ∃ r₀ > 0, ∀ r ∈ Ioo 0 r₀,
      CircleIntegrable g x r ∧ Real.circleAverage g x r ≤ g x := by
    intro x hx
    obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hU x hx
    by_cases hxb : x ∈ ball c ρ
    · have hxc : dist x c < ρ := hxb
      refine ⟨min r₁ (ρ - dist x c), lt_min hr₁ (by linarith), fun r hr => ?_⟩
      have hr0 : 0 < r := hr.1
      have hr1 : r < r₁ := lt_of_lt_of_le hr.2 (min_le_left _ _)
      have hr2 : r < ρ - dist x c := lt_of_lt_of_le hr.2 (min_le_right _ _)
      have hsubU : closedBall x r ⊆ U := (closedBall_subset_ball hr1).trans hball
      refine ⟨hint x r hr0 hsubU, ?_⟩
      have hsub' : closedBall x |r| ⊆ ball c ρ := by
        rw [abs_of_pos hr0]; exact closedBall_subset_ball' (by linarith)
      have heq : EqOn g (discPoissonIntegral u c ρ) (sphere x |r|) := fun y hy =>
        poissonModification_of_mem (hsub' (sphere_subset_closedBall hy))
      rw [Real.circleAverage_congr_sphere heq, circleAverage_discPoissonIntegral hui hsub', hgmem _ hxb]
    · refine ⟨r₁, hr₁, fun r hr => ?_⟩
      have hsubU : closedBall x r ⊆ U := (closedBall_subset_ball hr.2).trans hball
      obtain ⟨hui', hum⟩ := hu.2 x hx r hr.1 hsubU
      refine ⟨hint x r hr.1 hsubU, ?_⟩
      rw [hgnot _ hxb]
      exact (Real.circleAverage_mono (hint x r hr.1 hsubU) hui' fun y _ => hgle y).trans hum
  exact ⟨⟨hlsc, fun x hx r hr hsubx => ⟨hint x r hr hsubx,
    circleAverage_le_of_localSuperMean hlsc hloc' hr hsubx (hint x r hr hsubx)⟩⟩, hgle⟩

/-! ## The lower semicontinuous regularization of an infimum (AG01 Thm 3.7.5) -/

/-- The infimum of `f` over `B_{1/(n+1)}(w) ∩ U`. -/
noncomputable def localInf (U : Set ℂ) (f : ℂ → ℝ) (n : ℕ) (w : ℂ) : ℝ :=
  sInf (f '' (ball w (1 / ((n : ℝ) + 1)) ∩ U))

/-- The lower semicontinuous regularization `f̂(w) = liminf_{y → w, y ∈ U} f(y)` (for `w ∈ U`) of `f`, as the
supremum over `n` of the infima of `f` over `B_{1/(n+1)}(w) ∩ U`. -/
noncomputable def lscRegularization (U : Set ℂ) (f : ℂ → ℝ) (w : ℂ) : ℝ :=
  ⨆ n : ℕ, localInf U f n w

section LscRegularization

variable {U : Set ℂ} {f : ℂ → ℝ}

theorem bddBelow_localInf_set (hf0 : ∀ x ∈ U, 0 ≤ f x) (n : ℕ) (w : ℂ) :
    BddBelow (f '' (ball w (1 / ((n : ℝ) + 1)) ∩ U)) :=
  ⟨0, by rintro _ ⟨y, hy, rfl⟩; exact hf0 y hy.2⟩

theorem localInf_le_of_mem (hf0 : ∀ x ∈ U, 0 ≤ f x) {n : ℕ} {w y : ℂ}
    (hy : y ∈ ball w (1 / ((n : ℝ) + 1)) ∩ U) : localInf U f n w ≤ f y :=
  csInf_le (bddBelow_localInf_set hf0 n w) ⟨y, hy, rfl⟩

theorem localInf_le (hf0 : ∀ x ∈ U, 0 ≤ f x) (n : ℕ) {w : ℂ} (hw : w ∈ U) : localInf U f n w ≤ f w :=
  localInf_le_of_mem hf0 ⟨mem_ball_self (by positivity), hw⟩

theorem localInf_nonneg (hf0 : ∀ x ∈ U, 0 ≤ f x) (n : ℕ) {w : ℂ} (hw : w ∈ U) : 0 ≤ localInf U f n w :=
  le_csInf ⟨f w, w, ⟨mem_ball_self (by positivity), hw⟩, rfl⟩ (by rintro _ ⟨y, hy, rfl⟩; exact hf0 y hy.2)

/-- Comparison of local infima over nested balls. -/
theorem localInf_le_localInf (hf0 : ∀ x ∈ U, 0 ≤ f x) {n m : ℕ} {w w' : ℂ} (hw' : w' ∈ U)
    (hsub : ball w' (1 / ((m : ℝ) + 1)) ⊆ ball w (1 / ((n : ℝ) + 1))) :
    localInf U f n w ≤ localInf U f m w' :=
  csInf_le_csInf (bddBelow_localInf_set hf0 n w) ⟨f w', w', ⟨mem_ball_self (by positivity), hw'⟩, rfl⟩
    (image_mono (inter_subset_inter_left _ hsub))

theorem monotone_localInf (hf0 : ∀ x ∈ U, 0 ≤ f x) {w : ℂ} (hw : w ∈ U) :
    Monotone fun n => localInf U f n w := fun n m hnm =>
  localInf_le_localInf hf0 hw (ball_subset_ball (one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.succ_le_succ hnm)))

theorem bddAbove_localInf (hf0 : ∀ x ∈ U, 0 ≤ f x) {w : ℂ} (hw : w ∈ U) :
    BddAbove (range fun n => localInf U f n w) :=
  ⟨f w, by rintro _ ⟨n, rfl⟩; exact localInf_le hf0 n hw⟩

theorem lscRegularization_le (hf0 : ∀ x ∈ U, 0 ≤ f x) {w : ℂ} (hw : w ∈ U) :
    lscRegularization U f w ≤ f w :=
  ciSup_le fun n => localInf_le hf0 n hw

theorem localInf_le_lscRegularization (hf0 : ∀ x ∈ U, 0 ≤ f x) (n : ℕ) {w : ℂ} (hw : w ∈ U) :
    localInf U f n w ≤ lscRegularization U f w :=
  le_ciSup (bddAbove_localInf hf0 hw) n

theorem lscRegularization_nonneg (hf0 : ∀ x ∈ U, 0 ≤ f x) {w : ℂ} (hw : w ∈ U) :
    0 ≤ lscRegularization U f w :=
  (localInf_nonneg hf0 0 hw).trans (localInf_le_lscRegularization hf0 0 hw)

theorem tendsto_localInf (hf0 : ∀ x ∈ U, 0 ≤ f x) {w : ℂ} (hw : w ∈ U) :
    Tendsto (fun n => localInf U f n w) atTop (𝓝 (lscRegularization U f w)) :=
  tendsto_atTop_ciSup (monotone_localInf hf0 hw) (bddAbove_localInf hf0 hw)

/-- The lower semicontinuous regularization is lower semicontinuous on `U`. -/
theorem lowerSemicontinuousOn_lscRegularization (hf0 : ∀ x ∈ U, 0 ≤ f x) :
    LowerSemicontinuousOn (lscRegularization U f) U := by
  intro w hw a ha
  obtain ⟨n, hn⟩ := exists_lt_of_lt_ciSup ha
  have hball : ∀ᶠ w' in 𝓝[U] w, w' ∈ ball w (1 / ((2 * n + 1 : ℕ) + 1 : ℝ)) :=
    nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
  filter_upwards [hball, self_mem_nhdsWithin] with w' hw'b hw'U
  refine hn.trans_le ((localInf_le_localInf (m := 2 * n + 1) hf0 hw'U ?_).trans
    (localInf_le_lscRegularization hf0 (2 * n + 1) hw'U))
  intro y hy
  rw [mem_ball] at hy hw'b ⊢
  have e : (1 : ℝ) / ((2 * n + 1 : ℕ) + 1 : ℝ) = 1 / ((n : ℝ) + 1) / 2 := by
    push_cast; field_simp; ring
  rw [e] at hy hw'b
  calc dist y w ≤ dist y w' + dist w' w := dist_triangle _ _ _
    _ < 1 / ((n : ℝ) + 1) / 2 + 1 / ((n : ℝ) + 1) / 2 := add_lt_add hy hw'b
    _ = 1 / ((n : ℝ) + 1) := by ring

/-- A lower bound for `f` near `w` passes to the lower semicontinuous regularization at `w`. -/
theorem le_lscRegularization (hf0 : ∀ x ∈ U, 0 ≤ f x) {w : ℂ} (hw : w ∈ U) {a : ℝ}
    (h : ∀ ε > 0, ∀ᶠ y in 𝓝 w, y ∈ U → a - ε ≤ f y) : a ≤ lscRegularization U f w := by
  refine le_of_forall_sub_le fun ε hε => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h ε hε)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine le_trans ?_ (localInf_le_lscRegularization hf0 n hw)
  refine le_csInf ⟨f w, w, ⟨mem_ball_self (by positivity), hw⟩, rfl⟩ ?_
  rintro _ ⟨y, ⟨hy, hyU⟩, rfl⟩
  exact hball y (ball_subset_ball hn.le hy) hyU

/-- Measurability of the local infimum along a circle inside `U`: it is upper semicontinuous there. -/
theorem measurable_localInf_comp_circleMap (hf0 : ∀ x ∈ U, 0 ≤ f x) (n : ℕ) {x : ℂ} {r : ℝ}
    (hsph : sphere x |r| ⊆ U) : Measurable fun θ => localInf U f n (circleMap x r θ) := by
  refine UpperSemicontinuous.measurable fun θ a ha => ?_
  have hne : (f '' (ball (circleMap x r θ) (1 / ((n : ℝ) + 1)) ∩ U)).Nonempty :=
    ⟨_, _, ⟨mem_ball_self (by positivity), hsph (circleMap_mem_sphere' x r θ)⟩, rfl⟩
  obtain ⟨_, ⟨y, ⟨hy, hyU⟩, rfl⟩, hya⟩ := exists_lt_of_csInf_lt hne ha
  have hcont : ∀ᶠ θ' in 𝓝 θ, y ∈ ball (circleMap x r θ') (1 / ((n : ℝ) + 1)) := by
    have : ContinuousAt (fun θ' => dist y (circleMap x r θ')) θ := by fun_prop
    exact this.eventually (gt_mem_nhds (by simpa [mem_ball, dist_comm] using hy))
  filter_upwards [hcont] with θ' hθ'
  exact (localInf_le_of_mem hf0 ⟨hθ', hyU⟩).trans_lt hya

end LscRegularization

/-- **AG01 Thm 3.7.5** (lower semicontinuous regularization of an infimum; finite-valued form, family bounded below
by `0`). Let `𝒢` be a nonempty family of functions superharmonic on the open set `U`, and let `f ≥ 0` be its
pointwise infimum on `U`. Then the lower semicontinuous regularization `f̂` of `f` is superharmonic on `U`.
Proof: for `closedBall x r ⊆ U`, `n` large and `y ∈ B_{1/(n+1)}(x) ∩ U`, the local infimum of `f` on the circle
`∂B_r(x)` is pointwise below `g` on `∂B_r(y)` for every `g ∈ 𝒢`, so its circle average is `≤ g(y)`, hence
`≤ f(y)`, hence `≤ localInf U f n x ≤ f̂(x)`; let `n → ∞` (dominated convergence, bound `g₀`). -/
theorem isSuperharmonicOn_lscRegularization {U : Set ℂ} (hU : IsOpen U) {𝒢 : Set (ℂ → ℝ)}
    (h𝒢 : ∀ g ∈ 𝒢, IsSuperharmonicOn U g) {g₀ : ℂ → ℝ} (hg₀ : g₀ ∈ 𝒢) {f : ℂ → ℝ}
    (hf_le : ∀ g ∈ 𝒢, ∀ x ∈ U, f x ≤ g x) (hf_ge : ∀ x ∈ U, ∀ a : ℝ, (∀ g ∈ 𝒢, a ≤ g x) → a ≤ f x)
    (hf0 : ∀ x ∈ U, 0 ≤ f x) : IsSuperharmonicOn U (lscRegularization U f) := by
  refine ⟨lowerSemicontinuousOn_lscRegularization hf0, fun x hx r hr hsub => ?_⟩
  have hsph : sphere x |r| ⊆ U := fun y hy =>
    hsub (sphere_subset_closedBall (by rwa [abs_of_pos hr] at hy))
  have hg₀i : CircleIntegrable g₀ x r := ((h𝒢 g₀ hg₀).2 x hx r hr hsub).1
  -- bounds on the circle
  have hIle : ∀ n, ∀ y ∈ sphere x |r|, |localInf U f n y| ≤ g₀ y := fun n y hy => by
    rw [abs_of_nonneg (localInf_nonneg hf0 n (hsph hy))]
    exact (localInf_le hf0 n (hsph hy)).trans (hf_le g₀ hg₀ y (hsph hy))
  have hIi : ∀ n, CircleIntegrable (localInf U f n) x r := fun n =>
    IntervalIntegrable.mono_fun' hg₀i (measurable_localInf_comp_circleMap hf0 n hsph).aestronglyMeasurable
      (Eventually.of_forall fun θ => by
        simpa [Real.norm_eq_abs] using hIle n _ (circleMap_mem_sphere' x r θ))
  have hfhati : CircleIntegrable (lscRegularization U f) x r :=
    LowerSemicontinuousOn.circleIntegrable_of_le (lowerSemicontinuousOn_lscRegularization hf0) hsph
      (fun y hy => lscRegularization_nonneg hf0 (hsph hy))
      (fun y hy => (lscRegularization_le hf0 (hsph hy)).trans (hf_le g₀ hg₀ y (hsph hy))) hg₀i
  refine ⟨hfhati, ?_⟩
  -- the circle averages of the local infima converge
  have hlim := tendsto_circleAverage_of_dominated hIi hg₀i hIle
    (fun y hy => tendsto_localInf hf0 (hsph hy))
  obtain ⟨δ, hδ, hsubδ⟩ := exists_closedBall_add_subset hU hr.le hsub
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun n hn => ?_⟩)
  have hδn : 1 / ((n : ℝ) + 1) < δ :=
    lt_of_le_of_lt (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)) hN
  refine le_trans ?_ (localInf_le_lscRegularization hf0 n hx)
  refine le_csInf ⟨f x, x, ⟨mem_ball_self (by positivity), hx⟩, rfl⟩ ?_
  rintro _ ⟨y, ⟨hy, hyU⟩, rfl⟩
  have hyx : dist y x < 1 / ((n : ℝ) + 1) := hy
  have hsuby : closedBall y r ⊆ U := fun w hw => hsubδ (by
    rw [mem_closedBall] at hw ⊢
    linarith [dist_triangle w y x])
  refine hf_ge y hyU _ fun g hg => ?_
  obtain ⟨hgi, hgm⟩ := (h𝒢 g hg).2 y hyU r hr hsuby
  refine le_trans ?_ hgm
  simp only [Real.circleAverage_def, smul_eq_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine intervalIntegral.integral_mono_on Real.two_pi_pos.le (hIi n) hgi fun θ _ => ?_
  have hmem : circleMap y r θ ∈ ball (circleMap x r θ) (1 / ((n : ℝ) + 1)) ∩ U := by
    refine ⟨?_, hsuby (sphere_subset_closedBall ?_)⟩
    · have hd : dist (circleMap y r θ) (circleMap x r θ) = dist y x := by
        simp [circleMap, dist_eq_norm]
      rw [mem_ball, hd]
      exact hyx
    · simp [abs_of_pos hr]
  exact (localInf_le_of_mem hf0 hmem).trans (hf_le g hg _ hmem.2)

/-! ## Step 1 -/

/-- **Lemma A.1, Step 1** (lines 3602-3604), given Prop 2.3 and the continuity of `q_{B_R}`: every superharmonic
majorant of `β_t` is `≥ 0` on the closed ball. Minimum principle on `B_R`: `liminf g ≥ lim β_t = 0` at `∂B_R`
(`G_{B_R}(z, ·) → 0` and `q_{B_R} → 0`), and `g ≥ β_t = 0` on `∂B_R`. -/
theorem obstacleLeastSuperharmonicMajorantStep1_of (h23 : GreenFunctionBallStmt)
    (hq : GreenPotentialBallContinuousStep) : ObstacleLeastSuperharmonicMajorantStep1 := by
  intro μ hμ R βm βp hR hV z hz t ht g hg x hx
  have hqc := hq μ hμ R βm βp hR hV
  obtain ⟨-, -, hbd, -⟩ := h23 R hR z hz
  by_cases hxB : x ∈ ball (0 : ℂ) R
  · refine nonneg_of_lowerSemicontinuousOn_of_superMean hg.1.1
      (hg.1.localSuperMean isOpen_ball) (fun ξ hξ ε hε => ?_) x hxB
    have hG := (hbd ξ hξ).2
    have hqξ : Tendsto (greenPotentialBall μ R) (𝓝[ball 0 R] ξ) (𝓝 0) := by
      have h := (hqc ξ (sphere_subset_closedBall hξ)).mono_left
        (nhdsWithin_mono ξ (ball_subset_closedBall (x := (0 : ℂ)) (ε := R)))
      rwa [greenPotentialBall_eq_zero_of_notMem (by simp [mem_sphere_zero_iff_norm.1 hξ])] at h
    have hβ : Tendsto (obstacle μ R z t) (𝓝[ball 0 R] ξ) (𝓝 0) := by
      have h := (hG.const_mul (-t)).add hqξ
      have e : obstacle μ R z t = fun y => -t * greenFunction (ball 0 R) z y + greenPotentialBall μ R y := rfl
      rw [e]
      simpa using h
    have hzξ : ξ ≠ z := by
      rintro rfl
      simp [mem_sphere_zero_iff_norm.1 hξ] at hz
    filter_upwards [hβ.eventually (lt_mem_nhds (by linarith : -ε < 0)), self_mem_nhdsWithin,
      nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hzξ)] with y hy hyB hyz
    exact hy.trans_le (hg.2 y (ball_subset_closedBall hyB) hyz)
  · have hxz : x ≠ z := fun h => hxB (h ▸ hz)
    have h := hg.2 x hx hxz
    rwa [obstacle_eq_zero_of_notMem hxB] at h

/-! ## Step 2 -/

/-- **Lemma A.1, Step 2** (lines 3606-3620), given Prop 2.3 and the continuity of `q_{B_R}`: `f_t` is superharmonic
on `B_R`. If the admissible class is empty, `f_t = 0`. Otherwise `f_t ≥ 0` on the closed ball (Step 1), its lower
semicontinuous regularization `f̂_t` is superharmonic on `B_R` (`isSuperharmonicOn_lscRegularization`) and
`f̂_t ≥ β_t` on `B_R \ {z}` (continuity of `β_t` off the pole), so `f̂_t` on `B_R`, extended by `f_t`, is admissible;
hence `f_t ≤ f̂_t ≤ f_t` on `B_R`. -/
theorem obstacleLeastSuperharmonicMajorantStep2_of (h23 : GreenFunctionBallStmt)
    (hq : GreenPotentialBallContinuousStep) : ObstacleLeastSuperharmonicMajorantStep2 := by
  intro μ hμ R βm βp hR hV z hz t ht
  rcases (superharmonicMajorants μ R z t).eq_empty_or_nonempty with hF | ⟨g₀, hg₀⟩
  · refine (isSuperharmonicOn_zero _).congr fun x _ => ?_
    simp [lscLeastMajorant, hF]
  set F := superharmonicMajorants μ R z t with hFdef
  set f := lscLeastMajorant μ R z t with hfdef
  set U := ball (0 : ℂ) R with hUdef
  have h1 := obstacleLeastSuperharmonicMajorantStep1_of h23 hq μ hμ R βm βp hR hV z hz t ht
  have hbdd : ∀ x ∈ closedBall (0 : ℂ) R, BddBelow ((fun g : ℂ → ℝ => g x) '' F) := fun x hx =>
    ⟨0, by rintro _ ⟨g, hg, rfl⟩; exact h1 g hg x hx⟩
  have hne : ∀ x, ((fun g : ℂ → ℝ => g x) '' F).Nonempty := fun x => ⟨g₀ x, g₀, hg₀, rfl⟩
  have hf_le : ∀ g ∈ F, ∀ x ∈ closedBall (0 : ℂ) R, f x ≤ g x := fun g hg x hx =>
    csInf_le (hbdd x hx) ⟨g, hg, rfl⟩
  have hf_ge : ∀ x, ∀ a : ℝ, (∀ g ∈ F, a ≤ g x) → a ≤ f x := fun x a ha =>
    le_csInf (hne x) (by rintro _ ⟨g, hg, rfl⟩; exact ha g hg)
  have hf0U : ∀ x ∈ U, 0 ≤ f x := fun x hx =>
    hf_ge x 0 fun g hg => h1 g hg x (ball_subset_closedBall hx)
  have hfobs : ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → obstacle μ R z t x ≤ f x := fun x hx hxz =>
    hf_ge x _ fun g hg => hg.2 x hx hxz
  have hreg := isSuperharmonicOn_lscRegularization isOpen_ball (fun g hg => hg.1) hg₀
    (fun g hg x hx => hf_le g hg x (ball_subset_closedBall hx)) (fun x _ a ha => hf_ge x a ha) hf0U
  classical
  set ĝ : ℂ → ℝ := fun y => if y ∈ U then lscRegularization U f y else f y with hĝdef
  have hĝU : EqOn (lscRegularization U f) ĝ U := fun y hy => by simp [ĝ, hy]
  have hβc : ContinuousOn (obstacle μ R z t) (closedBall 0 R \ {z}) :=
    continuousOn_obstacle h23 hR hz (hq μ hμ R βm βp hR hV)
  have hĝF : ĝ ∈ F := by
    refine ⟨hreg.congr hĝU, fun x hx hxz => ?_⟩
    by_cases hxU : x ∈ U
    · rw [← hĝU hxU]
      refine le_lscRegularization hf0U hxU fun ε hε => ?_
      have hnhds : closedBall (0 : ℂ) R \ {z} ∈ 𝓝 x :=
        mem_of_superset ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hxU, hxz⟩)
          (fun y hy => ⟨ball_subset_closedBall hy.1, hy.2⟩)
      have hcont : ContinuousAt (obstacle μ R z t) x := hβc.continuousAt hnhds
      filter_upwards [hcont.eventually (Ioi_mem_nhds (by linarith : obstacle μ R z t x - ε <
        obstacle μ R z t x)), hnhds] with y hy hy' _
      exact (le_of_lt hy).trans (hfobs y hy'.1 hy'.2)
    · have hĝx : ĝ x = f x := by simp [ĝ, hxU]
      rw [hĝx]
      exact hfobs x hx hxz
  have hEq : EqOn (lscRegularization U f) f U := fun x hx =>
    le_antisymm (lscRegularization_le hf0U hx)
      ((hf_le ĝ hĝF x (ball_subset_closedBall hx)).trans (hĝU hx).symm.le)
  exact hreg.congr hEq

/-! ## Step 3 and its repair at the pole -/

/-- Common facts on `f_t` when the admissible class is nonempty (Step 1 and the definition as an infimum). -/
theorem lscLeastMajorant_facts (h23 : GreenFunctionBallStmt) (hq : GreenPotentialBallContinuousStep)
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t) {g₀ : ℂ → ℝ}
    (hg₀ : g₀ ∈ superharmonicMajorants μ R z t) :
    (∀ g ∈ superharmonicMajorants μ R z t, ∀ x ∈ closedBall (0 : ℂ) R, lscLeastMajorant μ R z t x ≤ g x) ∧
    (∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → obstacle μ R z t x ≤ lscLeastMajorant μ R z t x) ∧
    (∀ x ∈ closedBall (0 : ℂ) R, 0 ≤ lscLeastMajorant μ R z t x) := by
  have h1 := obstacleLeastSuperharmonicMajorantStep1_of h23 hq μ hμ R βm βp hR hV z hz t ht
  have hne : ∀ x, ((fun g : ℂ → ℝ => g x) '' superharmonicMajorants μ R z t).Nonempty := fun x =>
    ⟨g₀ x, g₀, hg₀, rfl⟩
  refine ⟨fun g hg x hx => csInf_le ⟨0, ?_⟩ ⟨g, hg, rfl⟩, fun x hx hxz => le_csInf (hne x) ?_,
    fun x hx => le_csInf (hne x) ?_⟩
  · rintro _ ⟨g', hg', rfl⟩; exact h1 g' hg' x hx
  · rintro _ ⟨g', hg', rfl⟩; exact hg'.2 x hx hxz
  · rintro _ ⟨g', hg', rfl⟩; exact h1 g' hg' x hx

/-- `f_t = 0` if the admissible class is empty (junk value of `sInf ∅`). -/
theorem lscLeastMajorant_eq_zero_of_empty {μ : Measure ℂ} {R : ℝ} {z : ℂ} {t : ℝ}
    (hF : superharmonicMajorants μ R z t = ∅) : lscLeastMajorant μ R z t = fun _ => 0 := by
  ext x; simp [lscLeastMajorant, hF]

/-- **Core of Step 3** (lines 3630-3647): if for every `ε > 0` there is a disc `closedBall x₀ δ ⊆ B_R` and a level `L`
with `L ≤ ε + f_t` on `∂B_δ(x₀)` and `β_t ≤ L` on `B_δ(x₀) \ {z}`, then `f_t` is upper semicontinuous at `x₀`: the
Poisson modification `g` of `ε + f_t` on `B_δ(x₀)` is admissible, so `f_t ≤ g`, and `g = P[ε + f_t]` is continuous
at `x₀` with `g(x₀) ≤ ε + f_t(x₀)`. -/
theorem upperSemicontinuousAt_lscLeastMajorant_of_poisson {μ : Measure ℂ} {R : ℝ} {z : ℂ} {t : ℝ}
    (hfle : ∀ g ∈ superharmonicMajorants μ R z t, ∀ x ∈ closedBall (0 : ℂ) R,
      lscLeastMajorant μ R z t x ≤ g x)
    (hfobs : ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → obstacle μ R z t x ≤ lscLeastMajorant μ R z t x)
    (hfsh : IsSuperharmonicOn (ball 0 R) (lscLeastMajorant μ R z t)) {x₀ : ℂ}
    (h : ∀ ε > 0, ∃ δ > 0, closedBall x₀ δ ⊆ ball 0 R ∧ ∃ L : ℝ,
      (∀ ζ ∈ sphere x₀ δ, L ≤ ε + lscLeastMajorant μ R z t ζ) ∧
      ∀ y ∈ ball x₀ δ, y ≠ z → obstacle μ R z t y ≤ L) :
    UpperSemicontinuousAt (lscLeastMajorant μ R z t) x₀ := by
  set f := lscLeastMajorant μ R z t with hfdef
  intro a ha
  have ha' : f x₀ < a := ha
  set ε := (a - f x₀) / 3 with hε
  have hε0 : 0 < ε := by simp only [ε]; linarith
  obtain ⟨δ, hδ, hsub, L, hL, hβL⟩ := h ε hε0
  set u : ℂ → ℝ := fun y => ε + f y with hudef
  have hu : IsSuperharmonicOn (ball 0 R) u := hfsh.const_add ε
  have hcU : x₀ ∈ ball (0 : ℂ) R := hsub (mem_closedBall_self hδ.le)
  have hui : CircleIntegrable u x₀ δ := (hu.2 x₀ hcU δ hδ hsub).1
  obtain ⟨hgsh, -⟩ := isSuperharmonicOn_poissonModification isOpen_ball hu hδ hsub
  have hgF : poissonModification u x₀ δ ∈ superharmonicMajorants μ R z t := by
    refine ⟨hgsh, fun y hy hyz => ?_⟩
    by_cases hyb : y ∈ ball x₀ δ
    · rw [poissonModification_of_mem hyb]
      exact (hβL y hyb hyz).trans (le_discPoissonIntegral hui hyb hL)
    · rw [poissonModification_of_notMem hyb]
      have := hfobs y hy hyz
      show obstacle μ R z t y ≤ ε + f y
      linarith
  have hPc : ContinuousAt (discPoissonIntegral u x₀ δ) x₀ :=
    (continuousOn_discPoissonIntegral hui).continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ))
  have hPx₀ : discPoissonIntegral u x₀ δ x₀ ≤ ε + f x₀ :=
    discPoissonIntegral_le hu.1 (hu.localSuperMean isOpen_ball) hδ hsub hui x₀ (mem_ball_self hδ)
  filter_upwards [hPc.eventually (gt_mem_nhds (show discPoissonIntegral u x₀ δ x₀ <
    discPoissonIntegral u x₀ δ x₀ + ε by linarith)), isOpen_ball.mem_nhds (mem_ball_self hδ)] with y hy hyb
  have h1 : f y ≤ poissonModification u x₀ δ y :=
    hfle _ hgF y (ball_subset_closedBall (hsub (ball_subset_closedBall hyb)))
  rw [poissonModification_of_mem hyb] at h1
  show f y < a
  linarith

/-- **Lemma A.1, Step 3 off the pole** (lines 3622-3647), given Prop 2.3 and the continuity of `q_{B_R}`. -/
theorem obstacleLeastSuperharmonicMajorantStep3_of (h23 : GreenFunctionBallStmt)
    (hq : GreenPotentialBallContinuousStep) : ObstacleLeastSuperharmonicMajorantStep3 := by
  intro μ hμ R βm βp hR hV z hz t ht x₀ hx₀ hx₀z
  rcases (superharmonicMajorants μ R z t).eq_empty_or_nonempty with hF | ⟨g₀, hg₀⟩
  · rw [lscLeastMajorant_eq_zero_of_empty hF]; exact upperSemicontinuousAt_const
  obtain ⟨hfle, hfobs, -⟩ := lscLeastMajorant_facts h23 hq hμ hR hV hz ht hg₀
  have hfsh := obstacleLeastSuperharmonicMajorantStep2_of h23 hq μ hμ R βm βp hR hV z hz t ht
  refine upperSemicontinuousAt_lscLeastMajorant_of_poisson hfle hfobs hfsh fun ε hε => ?_
  have hβc : ContinuousOn (obstacle μ R z t) (closedBall 0 R \ {z}) :=
    continuousOn_obstacle h23 hR hz (hq μ hμ R βm βp hR hV)
  have hnhds : closedBall (0 : ℂ) R \ {z} ∈ 𝓝 x₀ :=
    mem_of_superset ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hx₀, hx₀z⟩)
      (fun y hy => ⟨ball_subset_closedBall hy.1, hy.2⟩)
  obtain ⟨δ₁, hδ₁, hδ₁β⟩ := Metric.continuousAt_iff.1 (hβc.continuousAt hnhds) (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.1 (isOpen_ball.sdiff isClosed_singleton) x₀ ⟨hx₀, hx₀z⟩
  set δ := min (δ₁ / 2) (δ₂ / 2) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < δ₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ2 : δ < δ₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcb : closedBall x₀ δ ⊆ ball (0 : ℂ) R \ {z} := (closedBall_subset_ball hδ2).trans hδ₂sub
  refine ⟨δ, hδ0, hcb.trans sdiff_subset, obstacle μ R z t x₀ + ε / 2, fun ζ hζ => ?_, fun y hy _ => ?_⟩
  · have hζc := hcb (sphere_subset_closedBall hζ)
    have h1 := hδ₁β (show dist ζ x₀ < δ₁ by rw [mem_sphere] at hζ; linarith)
    have h2 := hfobs ζ (ball_subset_closedBall hζc.1) hζc.2
    rw [Real.dist_eq, abs_lt] at h1
    linarith
  · have h1 := hδ₁β (show dist y x₀ < δ₁ by rw [mem_ball] at hy; linarith)
    rw [Real.dist_eq, abs_lt] at h1
    linarith

/-- **Lemma A.1, Step 3 at the pole** (gap G2), given Prop 2.3, the continuity of `q_{B_R}` and
`ObstacleTendstoAtBotStep`: near the pole `β_t < ε ≤ ε + f_t`, so the Poisson modification of `ε + f_t` on a small
disc `B_δ(z)` is admissible with the level `L = ε`. -/
theorem obstacleLeastSuperharmonicMajorantStep4_of (h23 : GreenFunctionBallStmt)
    (hq : GreenPotentialBallContinuousStep) (hbot : ObstacleTendstoAtBotStep) :
    ObstacleLeastSuperharmonicMajorantStep4 := by
  intro μ hμ R βm βp hR hV z hz t ht
  rcases (superharmonicMajorants μ R z t).eq_empty_or_nonempty with hF | ⟨g₀, hg₀⟩
  · rw [lscLeastMajorant_eq_zero_of_empty hF]; exact upperSemicontinuousAt_const
  obtain ⟨hfle, hfobs, hf0⟩ := lscLeastMajorant_facts h23 hq hμ hR hV hz ht hg₀
  have hfsh := obstacleLeastSuperharmonicMajorantStep2_of h23 hq μ hμ R βm βp hR hV z hz t ht
  refine upperSemicontinuousAt_lscLeastMajorant_of_poisson hfle hfobs hfsh fun ε hε => ?_
  have hev : ∀ᶠ y in 𝓝[≠] z, obstacle μ R z t y < ε :=
    (hbot μ R z t hR hz ht (hq μ hμ R βm βp hR hV)).eventually (eventually_lt_atBot ε)
  obtain ⟨δ₁, hδ₁, hδ₁β⟩ := Metric.mem_nhdsWithin_iff.1 hev
  obtain ⟨δ₂, hδ₂, hδ₂sub⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
  set δ := min (δ₁ / 2) (δ₂ / 2) with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < δ₁ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ2 : δ < δ₂ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hcb : closedBall z δ ⊆ ball (0 : ℂ) R := (closedBall_subset_ball hδ2).trans hδ₂sub
  refine ⟨δ, hδ0, hcb, ε, fun ζ hζ => ?_, fun y hy hyz => ?_⟩
  · have := hf0 ζ (ball_subset_closedBall (hcb (sphere_subset_closedBall hζ)))
    linarith
  · exact (hδ₁β ⟨ball_subset_ball hδ1.le hy, hyz⟩).le

/-! ## The four steps -/

/-- **Shared step `GreenPotentialBallContinuousStep`** (property 1 of `q_{B_R}`, line 3538): continuity of `q_{B_R}`
on the closed ball, from the Hölder estimate `greenPotentialBall_continuousOn`
(Proofs/Potential/GreenPotentialHolder.lean). -/
theorem greenPotentialBallContinuousStep_holds : GreenPotentialBallContinuousStep :=
  greenPotentialBall_continuousOn

/-- **Lemma A.1, Step 1** (lines 3602-3604). -/
theorem obstacleLeastSuperharmonicMajorantStep1_holds : ObstacleLeastSuperharmonicMajorantStep1 :=
  obstacleLeastSuperharmonicMajorantStep1_of greenFunctionBall greenPotentialBallContinuousStep_holds

/-- **Lemma A.1, Step 2** (lines 3606-3620). -/
theorem obstacleLeastSuperharmonicMajorantStep2_holds : ObstacleLeastSuperharmonicMajorantStep2 :=
  obstacleLeastSuperharmonicMajorantStep2_of greenFunctionBall greenPotentialBallContinuousStep_holds

/-- **Lemma A.1, Step 3 off the pole** (lines 3622-3647). -/
theorem obstacleLeastSuperharmonicMajorantStep3_holds : ObstacleLeastSuperharmonicMajorantStep3 :=
  obstacleLeastSuperharmonicMajorantStep3_of greenFunctionBall greenPotentialBallContinuousStep_holds

/-- **Lemma A.1, Step 3 at the pole** (gap G2). -/
theorem obstacleLeastSuperharmonicMajorantStep4_holds : ObstacleLeastSuperharmonicMajorantStep4 :=
  obstacleLeastSuperharmonicMajorantStep4_of greenFunctionBall greenPotentialBallContinuousStep_holds
    obstacleTendstoAtBotStep_holds

/-- **Lemma A.1, general radius and pole**, given the remaining shared step `GreenPotentialBallLaplacianStep`
(`Δ q_{B_R} = -μ`, AG01 Thm 4.3.8): all other inputs of `obstacleLeastSuperharmonicMajorantGeneral_of_steps` are
proved. -/
theorem obstacleLeastSuperharmonicMajorantGeneral_of_laplacian (hΔq : GreenPotentialBallLaplacianStep) :
    ObstacleLeastSuperharmonicMajorantGeneral :=
  obstacleLeastSuperharmonicMajorantGeneral_of_steps superharmonicOfLaplacianLEStep_holds
    laplacianLEOfSuperharmonicStep_holds greenPotentialBallContinuousStep_holds hΔq
    obstacleLeastSuperharmonicMajorantStep1_holds obstacleLeastSuperharmonicMajorantStep2_holds
    obstacleLeastSuperharmonicMajorantStep3_holds obstacleLeastSuperharmonicMajorantStep4_holds

end HarmonicBalls
