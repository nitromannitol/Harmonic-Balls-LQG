import HarmonicBalls.FirstPass.S11r.RootedRootFinite
import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# Producers of `hLen` and `hμ` for the rooted certificate (task fp-S11at-hLen-hmu-producers, q1)

Route of `notes/fp-gaps/CHATGPT-211-hb-11-13-q1-hLen-hmu-PRO.md`, section 1 (`hLen`). The rooted insertion weight is
`rootedWeight α₀ γ z w = -α₀ log|w| - γ log|w - z| + γ log max(1,|w|)` (the weight of `rootedWeylMetric`, `S11at.lean`).
Term-by-term: the weight is continuous off `{0, z}`; its Weyl scaling is finite on the punctured plane `{0}ᶜ` by the
root-finite lemma `finite_on_disk_root` (Armitage-Gardiner-style connectedness; Duplantier-Sheffield Fact 2.2 (I) and (III)
in the form of Bou-Rabee-Gwynne arXiv:2208.11795). The point `0` is handled separately (not yet in this file).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open HarmonicBalls

namespace FirstPassS11atProducers

/-- The rooted insertion weight `w ↦ -α₀ log|w| - γ log|w - z| + γ log max(1,|w|)` (log-singular at `0` with strength
`α₀` and at the root `z` with strength `γ`; Duplantier-Sheffield, Berestycki-Powell convention). -/
noncomputable def rootedWeight (α₀ γ : ℝ) (z : ℂ) : ℂ → ℝ :=
  fun w => -α₀ * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)

/-- The rooted weight is continuous off `{0, z}`. -/
theorem rootedWeight_continuousOn_compl_zero_root (α₀ γ : ℝ) {z : ℂ} :
    ContinuousOn (rootedWeight α₀ γ z) ({0}ᶜ \ {z}) := by
  intro w hw
  have hw0 : w ≠ 0 := by simpa using hw.1
  have hwz : w ≠ z := by simpa using hw.2
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hnz : ‖w - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwz)
  have hm : max 1 ‖w‖ ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  have c1 : ContinuousAt (fun v : ℂ => Real.log ‖v‖) w :=
    (by fun_prop : Continuous fun v : ℂ => ‖v‖).continuousAt.log hn
  have c2 : ContinuousAt (fun v : ℂ => Real.log ‖v - z‖) w :=
    (by fun_prop : Continuous fun v : ℂ => ‖v - z‖).continuousAt.log hnz
  have c3 : ContinuousAt (fun v : ℂ => Real.log (max 1 ‖v‖)) w :=
    (by fun_prop : Continuous fun v : ℂ => max 1 ‖v‖).continuousAt.log hm
  exact (((continuousAt_const.mul c1).sub (continuousAt_const.mul c2)).add
    (continuousAt_const.mul c3)).continuousWithinAt

/-- **Finiteness of the rooted Weyl scaling on the punctured plane** (`hLen`, Steps 2-3 of Chat 211 section 1).
For a Euclidean length metric `d` and a root `z ≠ 0` at which the Weyl scaling of the rooted weight tends to `0`
in `ENNReal` (the frozen rooted insertion continuity, `RootedPhysicalMetricContinuousAtInsertionFrozen`), the rooted
Weyl scaling is finite on `{0}ᶜ`. Proof: `finite_on_disk_root` on the connected open set `{0}ᶜ`. -/
theorem weylScaling_rootedWeight_ne_top_punctured {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ α₀ γ : ℝ)
    {z : ℂ} (hz : z ≠ 0)
    (hW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) x z) (𝓝 z) (𝓝 0)) :
    ∀ x ∈ ({0}ᶜ : Set ℂ), ∀ y ∈ ({0}ᶜ : Set ℂ), weylScaling d ξ (rootedWeight α₀ γ z) x y ≠ ⊤ := by
  have hconn : IsConnected ({0}ᶜ : Set ℂ) := isConnected_compl_singleton_of_one_lt_rank (by simp) 0
  have hzD : z ∈ ({0}ᶜ : Set ℂ) := by simpa using hz
  exact (finite_on_disk_root hd ξ isOpen_compl_singleton hconn hzD
    (rootedWeight_continuousOn_compl_zero_root α₀ γ) hW).1

/-! ### The point `0`: finiteness and continuity (Step 4 of Chat 211, section 1) -/

/-- The insertion weight `w ↦ -α₀ log|w|` at `0`; its Weyl scaling is the metric `Dα` of Fact 2.2 I
(`LQGMetricFieldAxiomsUnivFrozen`, clause I). -/
noncomputable def alphaWeight (α₀ : ℝ) : ℂ → ℝ :=
  fun w => -α₀ * Real.log ‖w‖

/-- The root factor `w ↦ -γ log|w - z| + γ log max(1,|w|)` of the rooted weight, continuous off `z`. -/
noncomputable def rootFactor (γ : ℝ) (z : ℂ) : ℂ → ℝ :=
  fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)

theorem rootedWeight_eq_alpha_add_rootFactor (α₀ γ : ℝ) (z w : ℂ) :
    rootedWeight α₀ γ z w = alphaWeight α₀ w + rootFactor γ z w := by
  simp only [rootedWeight, alphaWeight, rootFactor]
  ring

theorem rootFactor_continuousOn (γ : ℝ) (z : ℂ) : ContinuousOn (rootFactor γ z) ({z}ᶜ : Set ℂ) := by
  intro w hw
  have hwz : w ≠ z := by simpa using hw
  have hnz : ‖w - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwz)
  have hm : max 1 ‖w‖ ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  have c2 : ContinuousAt (fun v : ℂ => Real.log ‖v - z‖) w :=
    (by fun_prop : Continuous fun v : ℂ => ‖v - z‖).continuousAt.log hnz
  have c3 : ContinuousAt (fun v : ℂ => Real.log (max 1 ‖v‖)) w :=
    (by fun_prop : Continuous fun v : ℂ => max 1 ‖v‖).continuousAt.log hm
  exact ((continuousAt_const.mul c2).add (continuousAt_const.mul c3)).continuousWithinAt

/-- Bound for the root factor on a ball about `0` not containing the root: `ξ · rootFactor` is bounded above on
`closedBall 0 r` when `r < ‖z‖` (continuity on a compact set). -/
theorem rootFactor_le_bound (ξ γ : ℝ) {z : ℂ} {r : ℝ} (hr : r < ‖z‖) :
    ∃ B : ℝ, ∀ w ∈ closedBall (0 : ℂ) r, ξ * rootFactor γ z w ≤ B := by
  have hsub : closedBall (0 : ℂ) r ⊆ ({z}ᶜ : Set ℂ) := by
    intro w hw
    simp only [mem_compl_iff, mem_singleton_iff]
    rintro rfl
    rw [mem_closedBall_zero_iff] at hw
    linarith
  have hK : ContinuousOn (fun w => ξ * rootFactor γ z w) (closedBall (0 : ℂ) r) :=
    continuousOn_const.mul ((rootFactor_continuousOn γ z).mono hsub)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn hK
  exact ⟨C, fun w hw => (le_abs_self _).trans (hC w hw)⟩

/-- Euclidean continuity at a point for a nonnegative Euclidean length metric: the `E`-balls about `z` are
Euclidean neighbourhoods of `z` (`isOpen_iff` of `IsEuclideanLengthMetric`, triangle inequality). -/
theorem tendsto_nhds_zero_of_isEuclideanLengthMetric {E : ℂ → ℂ → ℝ} (hE : IsEuclideanLengthMetric E)
    (hE0 : ∀ u v, 0 ≤ E u v) (z : ℂ) : Tendsto (fun w => E z w) (𝓝 z) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall (fun w => lt_of_lt_of_le ha (hE0 z w)), fun η hη => ?_⟩
  have hopen : IsOpen {w : ℂ | E z w < η} := by
    rw [hE.isOpen_iff]
    intro w hw
    have hw' : E z w < η := hw
    refine ⟨η - E z w, by linarith, fun w' hw'' => ?_⟩
    have htri := hE.triangle z w w'
    show E z w' < η
    linarith
  have hzmem : z ∈ {w : ℂ | E z w < η} := by
    show E z z < η
    rw [hE.self_eq_zero]
    exact hη
  exact hopen.mem_nhds hzmem

/-- Confinement at `0` (Fact 2.2 I for `Dα`): `W_α(0,·)` is at least some `ε > 0` off `ball 0 r`, because the
`Dα`-ball of small radius about `0` lies in `ball 0 r` (the metric `Dα` induces the Euclidean topology). -/
theorem weylScaling_alpha_ge_off_ball {d : ℂ → ℂ → ℝ} {ξ α₀ : ℝ}
    (hA : IsEuclideanLengthMetric (fun u v => (weylScaling d ξ (alphaWeight α₀) u v).toReal))
    (hfin : ∀ u v, weylScaling d ξ (alphaWeight α₀) u v ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y ∉ ball (0 : ℂ) r, ENNReal.ofReal ε ≤ weylScaling d ξ (alphaWeight α₀) 0 y := by
  obtain ⟨ε, hε, h⟩ := (hA.isOpen_iff (ball (0 : ℂ) r)).1 isOpen_ball 0 (mem_ball_self hr)
  refine ⟨ε, hε, fun y hy => ?_⟩
  have hlt : ε ≤ (weylScaling d ξ (alphaWeight α₀) 0 y).toReal := by
    by_contra hlt
    exact hy (h y (not_le.1 hlt))
  exact (ENNReal.ofReal_le_iff_le_toReal (hfin 0 y)).2 hlt

/-- Prefix comparison: the Weyl scaling from `x` to `p t` is at most the `f`-cost of the length-parametrized prefix
`p|[0,t]` of `p|[0,T]`. -/
theorem weylScaling_le_prefix_cost {d : ℂ → ℂ → ℝ} (ξ : ℝ) (f : ℂ → ℝ) {x : ℂ} {p : ℝ → ℂ} {T t : ℝ}
    (hp : IsLengthParametrized d p T) (h0 : p 0 = x) (ht : t ∈ Icc 0 T) :
    weylScaling d ξ f x (p t) ≤ ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p s))) := by
  have hpt : IsLengthParametrized d p t :=
    ⟨ht.1, hp.2.1.mono (Icc_subset_Icc le_rfl ht.2),
      fun s t' hs hst ht' => hp.2.2 s t' hs hst (ht'.trans ht.2)⟩
  unfold weylScaling
  refine (iInf₂_le t p).trans ((iInf₂_le hpt h0).trans ((iInf_le _ rfl).trans ?_))
  exact lintegral_mono_set (Icc_subset_Icc le_rfl ht.2)

/-- **Confined comparison at `0`** (Chat 211 section 1, Step 4). Let `B` bound `ξ · rootFactor` on `closedBall 0 r` and
let `ε` be the confinement constant of `weylScaling_alpha_ge_off_ball`. If `W_α(0,x) < b ≤ ε`, then
`W_F(0,x) ≤ exp B · b`: a near-optimal `Dα`-path from `0` stays in `ball 0 r`, where the rooted weight is at most
`exp B` times the `Dα` weight. -/
theorem weylScaling_rootedWeight_zero_le_of_lt {d : ℂ → ℂ → ℝ} (ξ α₀ γ : ℝ) {z : ℂ} {r B ε : ℝ}
    (hB : ∀ w ∈ closedBall (0 : ℂ) r, ξ * rootFactor γ z w ≤ B)
    (hε : ∀ y ∉ ball (0 : ℂ) r, ENNReal.ofReal ε ≤ weylScaling d ξ (alphaWeight α₀) 0 y)
    {x : ℂ} {b : ENNReal} (hxb : weylScaling d ξ (alphaWeight α₀) 0 x < b) (hb : b ≤ ENNReal.ofReal ε) :
    weylScaling d ξ (rootedWeight α₀ γ z) 0 x ≤ ENNReal.ofReal (Real.exp B) * b := by
  have hxb' := hxb
  unfold weylScaling at hxb'
  obtain ⟨T, hT⟩ := iInf_lt_iff.1 hxb'
  obtain ⟨p, hp⟩ := iInf_lt_iff.1 hT
  obtain ⟨hpL, hp'⟩ := iInf_lt_iff.1 hp
  obtain ⟨h0, hp''⟩ := iInf_lt_iff.1 hp'
  obtain ⟨hxT, hcost⟩ := iInf_lt_iff.1 hp''
  have hin : ∀ t ∈ Icc 0 T, p t ∈ ball (0 : ℂ) r := by
    intro t ht
    by_contra hout
    have h1 := hε (p t) hout
    have h2 := weylScaling_le_prefix_cost ξ (alphaWeight α₀) hpL h0 ht
    exact lt_irrefl _ ((h1.trans h2).trans_lt (hcost.trans_le hb))
  have hup : weylScaling d ξ (rootedWeight α₀ γ z) 0 x ≤
      ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * rootedWeight α₀ γ z (p s))) := by
    unfold weylScaling
    exact (iInf₂_le T p).trans ((iInf₂_le hpL h0).trans (iInf_le _ hxT))
  have hpt : ∀ s ∈ Icc 0 T, ENNReal.ofReal (Real.exp (ξ * rootedWeight α₀ γ z (p s))) ≤
      ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (Real.exp (ξ * alphaWeight α₀ (p s))) := by
    intro s hs
    have hBs := hB (p s) (ball_subset_closedBall (hin s hs))
    rw [← ENNReal.ofReal_mul (Real.exp_pos B).le]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    rw [rootedWeight_eq_alpha_add_rootFactor, mul_add]
    linarith
  calc weylScaling d ξ (rootedWeight α₀ γ z) 0 x
      ≤ ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * rootedWeight α₀ γ z (p s))) := hup
    _ ≤ ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (Real.exp (ξ * alphaWeight α₀ (p s))) :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ = ENNReal.ofReal (Real.exp B) * ∫⁻ s in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * alphaWeight α₀ (p s))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp B) * b := mul_le_mul_of_nonneg_left hcost.le (zero_le)

/-- Density form of `weylScaling_rootedWeight_zero_le_of_lt`: `W_F(0,x) ≤ exp B · W_α(0,x)` once `W_α(0,x) < ε`. -/
theorem weylScaling_rootedWeight_zero_le_mul {d : ℂ → ℂ → ℝ} (ξ α₀ γ : ℝ) {z : ℂ} {r B ε : ℝ}
    (hB : ∀ w ∈ closedBall (0 : ℂ) r, ξ * rootFactor γ z w ≤ B)
    (hε : ∀ y ∉ ball (0 : ℂ) r, ENNReal.ofReal ε ≤ weylScaling d ξ (alphaWeight α₀) 0 y) {x : ℂ}
    (hxε : weylScaling d ξ (alphaWeight α₀) 0 x < ENNReal.ofReal ε) :
    weylScaling d ξ (rootedWeight α₀ γ z) 0 x ≤
      ENNReal.ofReal (Real.exp B) * weylScaling d ξ (alphaWeight α₀) 0 x := by
  have : NeBot (𝓝[>] (weylScaling d ξ (alphaWeight α₀) 0 x)) :=
    nhdsGT_neBot_of_exists_gt ⟨_, hxε⟩
  have hcont : Tendsto (fun b : ENNReal => ENNReal.ofReal (Real.exp B) * b)
      (𝓝[>] (weylScaling d ξ (alphaWeight α₀) 0 x))
      (𝓝 (ENNReal.ofReal (Real.exp B) * weylScaling d ξ (alphaWeight α₀) 0 x)) :=
    ENNReal.Tendsto.const_mul (tendsto_id.mono_left nhdsWithin_le_nhds) (Or.inr ENNReal.ofReal_ne_top)
  refine ge_of_tendsto hcont ?_
  filter_upwards [Ioo_mem_nhdsGT hxε] with b hb
  exact weylScaling_rootedWeight_zero_le_of_lt ξ α₀ γ hB hε hb.1 hb.2.le

/-- **Step 4 of Chat 211 section 1.** At the point `0` the rooted Weyl scaling is finite everywhere and tends to `0`
in `ENNReal`, given the Dα length-metric input (`hA`, `hfin`: clause I of `LQGMetricFieldAxiomsUnivFrozen`) and the
root-continuity input at `z ≠ 0` (`hW`: `RootedPhysicalMetricContinuousAtInsertionFrozen`). -/
theorem weylScaling_rootedWeight_zero_finite_and_tendsto {d : ℂ → ℂ → ℝ} (ξ α₀ γ : ℝ) {z : ℂ}
    (hd : IsEuclideanLengthMetric d) (hz : z ≠ 0)
    (hW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) x z) (𝓝 z) (𝓝 0))
    (hA : IsEuclideanLengthMetric (fun u v => (weylScaling d ξ (alphaWeight α₀) u v).toReal))
    (hfin : ∀ u v, weylScaling d ξ (alphaWeight α₀) u v ≠ ⊤) :
    (∀ x, weylScaling d ξ (rootedWeight α₀ γ z) 0 x ≠ ⊤) ∧
      Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) 0 x) (𝓝 0) (𝓝 0) := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hr : 0 < ‖z‖ / 2 := by positivity
  have hrz : ‖z‖ / 2 < ‖z‖ := by linarith
  obtain ⟨B, hB⟩ := rootFactor_le_bound ξ γ hrz
  obtain ⟨ε, hε0, hε⟩ := weylScaling_alpha_ge_off_ball hA hfin hr
  have hWα : Tendsto (fun x => weylScaling d ξ (alphaWeight α₀) 0 x) (𝓝 0) (𝓝 0) := by
    have h1 := ENNReal.tendsto_ofReal
      (tendsto_nhds_zero_of_isEuclideanLengthMetric hA (fun u v => ENNReal.toReal_nonneg) 0)
    rw [ENNReal.ofReal_zero] at h1
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun x => ENNReal.ofReal_toReal (hfin 0 x)) h1
  have hlt : ∀ᶠ x in 𝓝 (0 : ℂ), weylScaling d ξ (alphaWeight α₀) 0 x < ENNReal.ofReal ε :=
    (tendsto_order.1 hWα).2 _ (ENNReal.ofReal_pos.2 hε0)
  have hzC : ∀ᶠ q in 𝓝 (0 : ℂ), q ∈ ({z}ᶜ : Set ℂ) :=
    isOpen_compl_singleton.mem_nhds (show (0 : ℂ) ∈ ({z}ᶜ : Set ℂ) from hz.symm)
  have hfinite : ∀ x, weylScaling d ξ (rootedWeight α₀ γ z) 0 x ≠ ⊤ := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [weylScaling_self_eq_zero hd]
      exact ENNReal.zero_ne_top
    · obtain ⟨q, hqlt, hqz, hq0⟩ : ∃ q : ℂ, weylScaling d ξ (alphaWeight α₀) 0 q < ENNReal.ofReal ε ∧
          q ∈ ({z}ᶜ : Set ℂ) ∧ q ∈ ({0}ᶜ : Set ℂ) := by
        have hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), weylScaling d ξ (alphaWeight α₀) 0 q < ENNReal.ofReal ε ∧
            q ∈ ({z}ᶜ : Set ℂ) ∧ q ∈ ({0}ᶜ : Set ℂ) := by
          filter_upwards [nhdsWithin_le_nhds (hlt.and hzC), self_mem_nhdsWithin] with q h1 h2
          exact ⟨h1.1, h1.2, h2⟩
        exact hev.exists
      have hqfin : weylScaling d ξ (rootedWeight α₀ γ z) 0 q ≠ ⊤ :=
        ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin 0 q))
          (weylScaling_rootedWeight_zero_le_mul ξ α₀ γ hB hε hqlt)
      have hxfin : weylScaling d ξ (rootedWeight α₀ γ z) q x ≠ ⊤ :=
        weylScaling_rootedWeight_ne_top_punctured hd ξ α₀ γ hz hW q hq0 x hx
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hqfin, hxfin⟩)
        (IsEuclideanLengthMetric.weylScaling_triangle hd ξ _ 0 q x)
  have hTW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) 0 x) (𝓝 0) (𝓝 0) := by
    have hc : Tendsto (fun x => ENNReal.ofReal (Real.exp B) * weylScaling d ξ (alphaWeight α₀) 0 x) (𝓝 0)
        (𝓝 (ENNReal.ofReal (Real.exp B) * 0)) :=
      ENNReal.Tendsto.const_mul hWα (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at hc
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc ?_ ?_
    · exact Filter.Eventually.of_forall fun _ => zero_le
    · filter_upwards [hlt] with x hx
      exact weylScaling_rootedWeight_zero_le_mul ξ α₀ γ hB hε hx
  exact ⟨hfinite, hTW⟩

/-! ### Local control at every point (Step 5 of Chat 211 section 1): annulus barrier and near-geodesic bound -/

/-- **Annulus barrier** (Chat 211 Step 5). If the weight is at least `m` on the annulus `δ' < dist(·, x) < δ`, if the
`d`-distance from `x` to the exterior `{dist(·,x) ≥ δ}` is at least `s`, and if the `d`-distance from `x` to the inner
disc `{dist(·,x) ≤ δ'}` is below `s / 2`, then every path from `x` to a point `w` with `δ ≤ dist(w,x)` has `f`-cost at least
`m * (s / 2)`. The path must cross the annulus; the crossing is at least `s / 2` long (triangle inequality and
`dist_le_of_lengthParametrized`) and carries weight at least `m`. -/
theorem weylScaling_ge_of_barrier {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (f : ℂ → ℝ)
    {x w : ℂ} {δ' δ s m : ℝ} (hδ' : 0 < δ') (hm : 0 < m)
    (hann : ∀ u : ℂ, δ' < dist u x → dist u x < δ → m ≤ Real.exp (ξ * f u))
    (hout : ∀ u : ℂ, δ ≤ dist u x → s ≤ d x u)
    (hin : ∀ u : ℂ, dist u x ≤ δ' → d x u < s / 2)
    (hw : δ ≤ dist w x) :
    ENNReal.ofReal (m * (s / 2)) ≤ weylScaling d ξ f x w := by
  unfold weylScaling
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT => ?_
  have hT0 : 0 ≤ T := hp.1
  have hcont : ContinuousOn p (Icc 0 T) := hp.2.1
  have hS0c : IsClosed (Icc 0 T ∩ p ⁻¹' closedBall x δ') :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  have hS0ne : (Icc 0 T ∩ p ⁻¹' closedBall x δ').Nonempty :=
    ⟨0, ⟨⟨le_rfl, hT0⟩, by rw [mem_preimage, h0]; exact mem_closedBall_self hδ'.le⟩⟩
  have hS0bdd : BddAbove (Icc 0 T ∩ p ⁻¹' closedBall x δ') := ⟨T, fun t ht => ht.1.2⟩
  have hτ0mem := hS0c.csSup_mem hS0ne hS0bdd
  have hτ0le : ∀ t ∈ Icc 0 T ∩ p ⁻¹' closedBall x δ', t ≤ sSup (Icc 0 T ∩ p ⁻¹' closedBall x δ') :=
    fun t ht => le_csSup hS0bdd ht
  obtain ⟨τ0, hτ0⟩ : ∃ τ0, τ0 = sSup (Icc 0 T ∩ p ⁻¹' closedBall x δ') := ⟨_, rfl⟩
  rw [← hτ0] at hτ0mem hτ0le
  have hτ0Icc : τ0 ∈ Icc 0 T := hτ0mem.1
  have hτ0d : dist (p τ0) x ≤ δ' := mem_closedBall.1 hτ0mem.2
  have hS1c : IsClosed (Icc τ0 T ∩ p ⁻¹' (ball x δ)ᶜ) :=
    (hcont.mono (Icc_subset_Icc hτ0Icc.1 le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
      isOpen_ball.isClosed_compl
  have hS1ne : (Icc τ0 T ∩ p ⁻¹' (ball x δ)ᶜ).Nonempty :=
    ⟨T, ⟨⟨hτ0Icc.2, le_rfl⟩, by
      rw [mem_preimage, hT]
      exact fun hb => absurd (mem_ball.1 hb) (not_lt.2 hw)⟩⟩
  have hS1bdd : BddBelow (Icc τ0 T ∩ p ⁻¹' (ball x δ)ᶜ) := ⟨τ0, fun t ht => ht.1.1⟩
  have hτ1mem := hS1c.csInf_mem hS1ne hS1bdd
  have hτ1le : ∀ t ∈ Icc τ0 T ∩ p ⁻¹' (ball x δ)ᶜ, sInf (Icc τ0 T ∩ p ⁻¹' (ball x δ)ᶜ) ≤ t :=
    fun t ht => csInf_le hS1bdd ht
  obtain ⟨τ1, hτ1⟩ : ∃ τ1, τ1 = sInf (Icc τ0 T ∩ p ⁻¹' (ball x δ)ᶜ) := ⟨_, rfl⟩
  rw [← hτ1] at hτ1mem hτ1le
  have hτ1Icc : τ1 ∈ Icc τ0 T := hτ1mem.1
  have hτ1out : δ ≤ dist (p τ1) x := not_lt.1 (fun h => hτ1mem.2 (mem_ball.2 h))
  have hτ01 : τ0 ≤ τ1 := hτ1Icc.1
  have hτ1T : τ1 ≤ T := hτ1Icc.2
  have hIoo : ∀ t ∈ Ioo τ0 τ1, m ≤ Real.exp (ξ * f (p t)) := by
    intro t ht
    have htIcc : t ∈ Icc 0 T := ⟨le_trans hτ0Icc.1 ht.1.le, le_trans ht.2.le hτ1T⟩
    apply hann
    · by_contra hcon
      have hcon' := not_lt.1 hcon
      have htS0 : t ∈ Icc 0 T ∩ p ⁻¹' closedBall x δ' := ⟨htIcc, mem_closedBall.2 hcon'⟩
      exact absurd ht.1 (not_lt.2 (hτ0le t htS0))
    · by_contra hcon
      have htS1 : t ∈ Icc τ0 T ∩ p ⁻¹' (ball x δ)ᶜ :=
        ⟨⟨ht.1.le, le_trans ht.2.le hτ1T⟩, fun hb => hcon (mem_ball.1 hb)⟩
      exact absurd ht.2 (not_lt.2 (hτ1le t htS1))
  have hτ1Icc0 : τ1 ∈ Icc 0 T := ⟨le_trans hτ0Icc.1 hτ1Icc.1, hτ1Icc.2⟩
  have hdlen : d (p τ0) (p τ1) ≤ τ1 - τ0 := by
    have h := hd.dist_le_of_lengthParametrized hp hτ0Icc hτ1Icc0
    rwa [abs_of_nonneg (sub_nonneg.2 hτ01)] at h
  have hsd : s ≤ d x (p τ1) := hout (p τ1) hτ1out
  have hd0 : d x (p τ0) < s / 2 := hin (p τ0) hτ0d
  have htri := hd.triangle x (p τ0) (p τ1)
  have hlen : s / 2 ≤ τ1 - τ0 := by linarith
  calc ENNReal.ofReal (m * (s / 2)) ≤ ENNReal.ofReal m * ENNReal.ofReal (τ1 - τ0) := by
        rw [← ENNReal.ofReal_mul hm.le]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hlen hm.le)
    _ = ∫⁻ _ in Ioo τ0 τ1, ENNReal.ofReal m := by
        rw [setLIntegral_const, Real.volume_Ioo]
    _ ≤ ∫⁻ t in Ioo τ0 τ1, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht => ENNReal.ofReal_le_ofReal (hIoo t ht)
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        lintegral_mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc hτ0Icc.1 hτ1T))

/-- Scales of the barrier at `x` (Euclidean topology of `d`, Fact 2.2 I): for every outer radius `ρ > 0` there are
`s > 0` with `d x u ≥ s` whenever `dist u x ≥ ρ`, and an inner radius `δ' > 0` with `d x u < s / 2` whenever
`dist u x ≤ δ'`. -/
theorem exists_barrier_scales {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (x : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ, 0 < s ∧ ∃ δ' : ℝ, 0 < δ' ∧ (∀ u : ℂ, ρ ≤ dist u x → s ≤ d x u) ∧
      (∀ u : ℂ, dist u x ≤ δ' → d x u < s / 2) := by
  obtain ⟨s, hs, hball⟩ := (hd.isOpen_iff (ball x ρ)).1 isOpen_ball x (mem_ball_self hρ)
  have hopen : IsOpen {u : ℂ | d x u < s / 2} := by
    refine (hd.isOpen_iff _).2 (fun u hu => ⟨s / 2 - d x u, by linarith [show d x u < s / 2 from hu],
      fun v hv => ?_⟩)
    have htri := hd.triangle x u v
    show d x v < s / 2
    linarith
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hopen x (show d x x < s / 2 by rw [hd.self_eq_zero]; linarith)
  refine ⟨s, hs, ε / 2, by linarith, fun u hu => ?_, fun u hu => ?_⟩
  · by_contra hcon
    have hu' := hball u (not_le.1 hcon)
    rw [mem_ball] at hu'
    linarith
  · have hmem : u ∈ ball x ε := by rw [mem_ball]; linarith
    exact hsub hmem

/-- Upper bound for the `d`-length-weighted cost near a point where the weight is bounded above (Chat 211 Step 5,
Fact 2.2 III): for `d x w` small, `W(x,w) ≤ exp B · (d x w + η)`. The near-geodesic path stays in a small `d`-ball, where
`ξ f ≤ B`. -/
theorem weylScaling_le_near {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (f : ℂ → ℝ)
    {x : ℂ} {ρ B : ℝ} (hρ : 0 < ρ) (hB : ∀ u : ℂ, dist u x ≤ ρ → ξ * f u ≤ B) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, d x w < δ → ∀ η : ℝ, 0 < η →
      weylScaling d ξ f x w ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (d x w + η) := by
  obtain ⟨s0, hs0, hball⟩ := (hd.isOpen_iff (ball x ρ)).1 isOpen_ball x (mem_ball_self hρ)
  have hnn : ∀ u v, 0 ≤ d u v := fun u v => by
    have h1 := hd.triangle u v u
    have h2 := hd.self_eq_zero u
    have h3 := hd.symm v u
    linarith
  refine ⟨s0 / 2, by linarith, fun w hw η hη => ?_⟩
  obtain ⟨T, p, hp, h0, hT, hTlt⟩ :=
    exists_lengthParametrized_lt_of_weylScaling_zero (fun a b => IsEuclideanLengthMetric.weylScaling_zero hd ξ a b)
      hnn x w (lt_min hη (by linarith : (0 : ℝ) < s0 / 2))
  have hT0 : 0 ≤ T := hp.1
  have hm2 : min η (s0 / 2) ≤ s0 / 2 := min_le_right _ _
  have hpt : ∀ t ∈ Icc 0 T, dist (p t) x ≤ ρ := by
    intro t ht
    have h1 := hd.dist_le_of_lengthParametrized hp (s := 0) (t := t) ⟨le_rfl, hT0⟩ ht
    rw [sub_zero, abs_of_nonneg ht.1, h0] at h1
    have hlt : d x (p t) < s0 := by linarith [ht.2]
    exact le_of_lt (mem_ball.1 (hball (p t) hlt))
  have hweight : ∀ t ∈ Icc 0 T, ξ * f (p t) ≤ B := fun t ht => hB (p t) (hpt t ht)
  have hW := weylScaling_le_of_lengthParametrized d ξ f hp h0 hT hweight
  calc weylScaling d ξ f x w ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal T := hW
    _ ≤ ENNReal.ofReal (Real.exp B) * ENNReal.ofReal (d x w + η) :=
        mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal (by linarith [min_le_left η (s0 / 2)])) zero_le

/-- Weight lower bound on an annulus (compactness; Chat 211 Step 5). If `f` is continuous on the closed annulus
`{δ' ≤ dist(·,x) ≤ δ}`, then `exp(ξ f)` has a positive minimum there. -/
theorem exists_annulus_lower_bound (ξ : ℝ) {f : ℂ → ℝ} {x : ℂ} {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (hf : ContinuousOn f (closedBall x δ ∩ {u : ℂ | δ' ≤ dist u x})) :
    ∃ m : ℝ, 0 < m ∧ ∀ u : ℂ, δ' < dist u x → dist u x < δ → m ≤ Real.exp (ξ * f u) := by
  have hKc : IsCompact (closedBall x δ ∩ {u : ℂ | δ' ≤ dist u x}) :=
    (isCompact_closedBall x δ).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  have hd' : dist (x + (δ' : ℂ)) x = δ' := by
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ']
  have hne : (closedBall x δ ∩ {u : ℂ | δ' ≤ dist u x}).Nonempty :=
    ⟨x + (δ' : ℂ), mem_closedBall.2 (by rw [hd']; exact hδ), by show δ' ≤ dist (x + (δ' : ℂ)) x; rw [hd']⟩
  have hg : ContinuousOn (fun u => Real.exp (ξ * f u)) (closedBall x δ ∩ {u : ℂ | δ' ≤ dist u x}) :=
    Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hf)
  obtain ⟨u0, hu0, hmin⟩ := hKc.exists_isMinOn hne hg
  refine ⟨Real.exp (ξ * f u0), Real.exp_pos _, fun u hu1 hu2 => ?_⟩
  exact isMinOn_iff.1 hmin u ⟨mem_closedBall.2 hu2.le, hu1.le⟩

/-- A radius avoiding the points `a`, `b` other than the centre `x` (Chat 211 Step 5: the annuli stay off the insertions). -/
theorem exists_avoid_radius (x a b : ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ ({a, b} : Set ℂ), q ≠ x → δ < dist q x := by
  have key : ∀ c : ℂ, ∃ δc : ℝ, 0 < δc ∧ (c ≠ x → δc < dist c x) := by
    intro c
    by_cases hc : c = x
    · exact ⟨1, one_pos, fun h => absurd hc h⟩
    · have hpos : 0 < dist c x := dist_pos.2 hc
      exact ⟨dist c x / 2, half_pos hpos, fun _ => by linarith⟩
  obtain ⟨δa, ha, hha⟩ := key a
  obtain ⟨δb, hb, hhb⟩ := key b
  refine ⟨min δa δb, lt_min ha hb, fun q hq hqx => ?_⟩
  rcases Set.mem_insert_iff.1 hq with h | h
  · have hax : a ≠ x := by rw [← h]; exact hqx
    rw [h]; exact lt_of_le_of_lt (min_le_left _ _) (hha hax)
  · have hq' := Set.mem_singleton_iff.1 h
    have hbx : b ≠ x := by rw [← hq']; exact hqx
    rw [hq']; exact lt_of_le_of_lt (min_le_right _ _) (hhb hbx)

theorem isEuclid_nonneg {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (u v : ℂ) : 0 ≤ d u v := by
  have h1 := hd.triangle u v u
  have h2 := hd.self_eq_zero u
  have h3 := hd.symm v u
  linarith

/-- The Euclidean balls of the length metric are open (Fact 2.2 I, `isOpen_iff`). -/
theorem isOpen_dist_lt {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (x : ℂ) (δ : ℝ) :
    IsOpen {w : ℂ | d x w < δ} := by
  refine (hd.isOpen_iff _).2 (fun u hu => ⟨δ - d x u, by linarith [show d x u < δ from hu], fun v hv => ?_⟩)
  have htri := hd.triangle x u v
  show d x v < δ
  linarith

/-- Points of a closed annulus about `x` of outer radius `δ` avoid the points `a`, `b ≠ x`. -/
theorem annulus_avoids {x a b : ℂ} {δ δ'' : ℝ} (hδ : ∀ q ∈ ({a, b} : Set ℂ), q ≠ x → δ < dist q x)
    (hδ'' : 0 < δ'') {u : ℂ} (hu1 : dist u x ≤ δ) (hu2 : δ'' ≤ dist u x) : u ≠ a ∧ u ≠ b := by
  constructor
  · intro hua
    by_cases hax : a = x
    · rw [hua, hax, dist_self] at hu2
      linarith
    · have h := hδ a (Set.mem_insert _ _) hax
      rw [hua] at hu1
      linarith
  · intro hub
    by_cases hbx : b = x
    · rw [hub, hbx, dist_self] at hu2
      linarith
    · have h := hδ b (Set.mem_insert_of_mem _ (Set.mem_singleton _)) hbx
      rw [hub] at hu1
      linarith

/-- **Generic Euclidean continuity at a point** (Chat 211 Step 5, from the upper bound): if the nonnegative
function `E` satisfies `E w ≤ c (d x w + η)` for `d x w < δ(η)`, then `E → 0` along the Euclidean topology. -/
theorem tendsto_of_near_bound {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (x : ℂ) {E : ℂ → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hE0 : ∀ w, 0 ≤ E w)
    (hbound : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, d x w < δ → E w ≤ c * (d x w + η)) :
    Tendsto E (𝓝 x) (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => Filter.Eventually.of_forall (fun w => lt_of_lt_of_le ha (hE0 w)), fun ε hε => ?_⟩
  have hc1 : (0 : ℝ) < 2 * (c + 1) := by linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ε / (2 * (c + 1)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; exact div_pos hε hc1
  have h2 : 2 * η * (c + 1) = ε := by
    rw [hηdef]; field_simp
  obtain ⟨δ, hδ, hb⟩ := hbound η hη
  have hx0 : x ∈ {w : ℂ | d x w < min δ η} := by
    show d x x < min δ η
    rw [hd.self_eq_zero]; exact lt_min hδ hη
  filter_upwards [(isOpen_dist_lt hd x (min δ η)).mem_nhds hx0] with w hw
  have hw' : d x w < min δ η := hw
  have hdδ : d x w < δ := lt_of_lt_of_le hw' (min_le_left _ _)
  have hdη : d x w < η := lt_of_lt_of_le hw' (min_le_right _ _)
  have hEw := hb w hdδ
  nlinarith [mul_nonneg hc (le_of_lt (sub_pos.2 hdη)), h2, hη, hEw]

/-- The rooted Weyl scaling at a point `x ∉ {0, z}` is Euclidean-continuous to `0` (upper bound of
`weylScaling_le_near` with the weight bounded above on a closed ball avoiding the insertions). -/
theorem tendsto_E_generic {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ α₀ γ : ℝ) {z x : ℂ}
    (hx0 : x ≠ 0) (hxz : x ≠ z) :
    Tendsto (fun w => (weylScaling d ξ (rootedWeight α₀ γ z) x w).toReal) (𝓝 x) (𝓝 0) := by
  obtain ⟨ρ, hρ, hav⟩ := exists_avoid_radius x 0 z
  have hρ' : 0 < ρ / 2 := half_pos hρ
  have hsub : closedBall x (ρ / 2) ⊆ ({0}ᶜ \ {z} : Set ℂ) := by
    intro u hu
    have hu' : dist u x ≤ ρ / 2 := hu
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h0 := Set.mem_singleton_iff.1 h
      rw [h0] at hu'
      have := hav 0 (Set.mem_insert _ _) (fun h' => hx0 h'.symm)
      linarith
    · have hz' := Set.mem_singleton_iff.1 h
      rw [hz'] at hu'
      have := hav z (Set.mem_insert_of_mem _ (Set.mem_singleton _)) (fun h' => hxz h'.symm)
      linarith
  have hcont : ContinuousOn (fun u => ξ * rootedWeight α₀ γ z u) (closedBall x (ρ / 2)) :=
    continuousOn_const.mul ((rootedWeight_continuousOn_compl_zero_root α₀ γ).mono hsub)
  obtain ⟨C, hC⟩ := (isCompact_closedBall x (ρ / 2)).exists_bound_of_continuousOn hcont
  have hB : ∀ u : ℂ, dist u x ≤ ρ / 2 → ξ * rootedWeight α₀ γ z u ≤ C :=
    fun u hu => (le_abs_self _).trans (hC u (mem_closedBall.2 hu))
  obtain ⟨δ, hδ, hbnd⟩ := weylScaling_le_near hd ξ (rootedWeight α₀ γ z) hρ' hB
  refine tendsto_of_near_bound hd x (c := Real.exp C) (Real.exp_pos C).le
    (fun w => ENNReal.toReal_nonneg) (fun η hη => ⟨δ, hδ, fun w hw => ?_⟩)
  have h1 := hbnd w hw η hη
  have hnn : 0 ≤ d x w + η := by linarith [isEuclid_nonneg hd x w]
  calc (weylScaling d ξ (rootedWeight α₀ γ z) x w).toReal
      ≤ (ENNReal.ofReal (Real.exp C) * ENNReal.ofReal (d x w + η)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) h1
    _ = Real.exp C * (d x w + η) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos C).le, ENNReal.toReal_ofReal hnn]

/-- At the point `0` (Step 4): the rooted Weyl scaling tends to `0` in the real topology. -/
theorem tendsto_E_zero {d : ℂ → ℂ → ℝ} (ξ α₀ γ : ℝ) {z : ℂ} (hd : IsEuclideanLengthMetric d) (hz : z ≠ 0)
    (hW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) x z) (𝓝 z) (𝓝 0))
    (hA : IsEuclideanLengthMetric (fun u v => (weylScaling d ξ (alphaWeight α₀) u v).toReal))
    (hfin : ∀ u v, weylScaling d ξ (alphaWeight α₀) u v ≠ ⊤) :
    Tendsto (fun w => (weylScaling d ξ (rootedWeight α₀ γ z) 0 w).toReal) (𝓝 0) (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (weylScaling_rootedWeight_zero_finite_and_tendsto ξ α₀ γ hd hz hW hA hfin).2
  rw [ENNReal.toReal_zero] at h
  exact h

/-- At the root `z`: the rooted Weyl scaling tends to `0` along the Euclidean topology (frozen continuity at the root,
and symmetry of the Weyl scaling). -/
theorem tendsto_E_root {d : ℂ → ℂ → ℝ} (ξ α₀ γ : ℝ) {z : ℂ} (hd : IsEuclideanLengthMetric d)
    (hW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) x z) (𝓝 z) (𝓝 0)) :
    Tendsto (fun w => (weylScaling d ξ (rootedWeight α₀ γ z) z w).toReal) (𝓝 z) (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hW
  rw [ENNReal.toReal_zero] at h
  refine Filter.Tendsto.congr (fun w => ?_) h
  simp only [Function.comp]
  rw [IsEuclideanLengthMetric.weylScaling_symm hd]

/-- The Euclidean limit at every point (Step 5, all cases). -/
theorem tendsto_E_all {d : ℂ → ℂ → ℝ} (ξ α₀ γ : ℝ) {z : ℂ} (hd : IsEuclideanLengthMetric d) (hz : z ≠ 0)
    (hW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) x z) (𝓝 z) (𝓝 0))
    (hA : IsEuclideanLengthMetric (fun u v => (weylScaling d ξ (alphaWeight α₀) u v).toReal))
    (hfin : ∀ u v, weylScaling d ξ (alphaWeight α₀) u v ≠ ⊤) (x : ℂ) :
    Tendsto (fun w => (weylScaling d ξ (rootedWeight α₀ γ z) x w).toReal) (𝓝 x) (𝓝 0) := by
  by_cases h0 : x = 0
  · subst h0
    exact tendsto_E_zero ξ α₀ γ hd hz hW hA hfin
  · by_cases hzx : x = z
    · subst hzx
      exact tendsto_E_root ξ α₀ γ hd hW
    · exact tendsto_E_generic hd ξ α₀ γ h0 hzx

/-- **Barrier at a point** (Chat 211 Step 5, separation and Euclidean openness). For every centre `x` and every
radius `r > 0` there are an outer radius `δ ∈ (0, r]` and `c > 0` with `c ≤ E x w` whenever `δ ≤ dist(w, x)`. -/
theorem barrier_at {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ α₀ γ : ℝ) {z x : ℂ}
    (hfinW : ∀ w : ℂ, weylScaling d ξ (rootedWeight α₀ γ z) x w ≠ ⊤) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ ∃ c : ℝ, 0 < c ∧
      ∀ w : ℂ, δ ≤ dist w x → c ≤ (weylScaling d ξ (rootedWeight α₀ γ z) x w).toReal := by
  obtain ⟨ρ, hρ, hav⟩ := exists_avoid_radius x 0 z
  have hδpos : 0 < min ρ r := lt_min hρ hr
  have hav' : ∀ q ∈ ({0, z} : Set ℂ), q ≠ x → min ρ r < dist q x :=
    fun q hq hqx => lt_of_le_of_lt (min_le_left _ _) (hav q hq hqx)
  obtain ⟨s, hs, δ', hδ', hout, hin⟩ := exists_barrier_scales hd x hδpos
  have hδ''pos : 0 < min δ' (min ρ r / 2) := lt_min hδ' (half_pos hδpos)
  have hδ''le : min δ' (min ρ r / 2) ≤ min ρ r :=
    le_trans (min_le_right _ _) (by linarith)
  have hsub : closedBall x (min ρ r) ∩ {u : ℂ | min δ' (min ρ r / 2) ≤ dist u x} ⊆
      ({0}ᶜ \ {z} : Set ℂ) := by
    rintro u ⟨hu1, hu2⟩
    rw [mem_closedBall] at hu1
    have hu2' : min δ' (min ρ r / 2) ≤ dist u x := hu2
    obtain ⟨h0, hz'⟩ := annulus_avoids hav' hδ''pos hu1 hu2'
    exact ⟨fun h => h0 (Set.mem_singleton_iff.1 h), fun h => hz' (Set.mem_singleton_iff.1 h)⟩
  obtain ⟨m, hm, hann⟩ := exists_annulus_lower_bound ξ hδ''pos hδ''le
    ((rootedWeight_continuousOn_compl_zero_root α₀ γ).mono hsub)
  have hbar : ∀ w : ℂ, min ρ r ≤ dist w x →
      ENNReal.ofReal (m * (s / 2)) ≤ weylScaling d ξ (rootedWeight α₀ γ z) x w :=
    fun w hw => weylScaling_ge_of_barrier hd ξ (rootedWeight α₀ γ z) hδ''pos hm hann hout
      (fun u hu => hin u (le_trans hu (min_le_left _ _))) hw
  refine ⟨min ρ r, hδpos, min_le_right _ _, m * (s / 2), mul_pos hm (half_pos hs), fun w hw => ?_⟩
  exact (ENNReal.ofReal_le_iff_le_toReal (hfinW w)).1 (hbar w hw)

/-- **Deterministic `hLen` (Chat 211 Steps 1-7, section 1).** For a Euclidean length metric `d` and a root `z ≠ 0`, the
rooted metric `(u, v) ↦ (weylScaling d ξ (rootedWeight α₀ γ z) u v).toReal` is a Euclidean length metric on the whole
plane. Inputs: the base metric `hd`; the Dα length-metric input `hA`, `hfin` (clause I of
`LQGMetricFieldAxiomsUnivFrozen`); the frozen root continuity `hW` (`RootedPhysicalMetricContinuousAtInsertionFrozen`). -/
theorem rootedWeight_isEuclideanLengthMetric_of_inputs {d : ℂ → ℂ → ℝ} (ξ α₀ γ : ℝ) {z : ℂ}
    (hd : IsEuclideanLengthMetric d) (hz : z ≠ 0)
    (hW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) x z) (𝓝 z) (𝓝 0))
    (hA : IsEuclideanLengthMetric (fun u v => (weylScaling d ξ (alphaWeight α₀) u v).toReal))
    (hfin : ∀ u v, weylScaling d ξ (alphaWeight α₀) u v ≠ ⊤) :
    IsEuclideanLengthMetric (fun x y => (weylScaling d ξ (rootedWeight α₀ γ z) x y).toReal) := by
  have hfin0 := weylScaling_rootedWeight_zero_finite_and_tendsto ξ α₀ γ hd hz hW hA hfin
  have hfinW : ∀ x y, weylScaling d ξ (rootedWeight α₀ γ z) x y ≠ ⊤ := by
    intro x y
    by_cases hx : x = 0
    · subst hx
      exact hfin0.1 y
    · by_cases hy : y = 0
      · subst hy
        rw [IsEuclideanLengthMetric.weylScaling_symm hd]
        exact hfin0.1 x
      · exact weylScaling_rootedWeight_ne_top_punctured hd ξ α₀ γ hz hW x hx y hy
  have hsymm : ∀ x y, weylScaling d ξ (rootedWeight α₀ γ z) x y = weylScaling d ξ (rootedWeight α₀ γ z) y x :=
    fun x y => IsEuclideanLengthMetric.weylScaling_symm hd ξ _ x y
  refine ⟨fun x => ?_, fun x y h0 => ?_, fun x y => ?_, fun x y w => ?_, fun U => ?_, fun x y => ?_⟩
  · show (weylScaling d ξ (rootedWeight α₀ γ z) x x).toReal = 0
    rw [weylScaling_self_eq_zero hd ξ _ x]
    simp
  · by_contra hxy
    have h0' : (weylScaling d ξ (rootedWeight α₀ γ z) x y).toReal = 0 := h0
    obtain ⟨δ, hδ, hδr, c, hc, hcle⟩ :=
      barrier_at hd ξ α₀ γ (fun w => hfinW x w) (dist_pos.2 (Ne.symm hxy))
    linarith [hcle y hδr]
  · show (weylScaling d ξ (rootedWeight α₀ γ z) x y).toReal = (weylScaling d ξ (rootedWeight α₀ γ z) y x).toReal
    rw [hsymm x y]
  · show (weylScaling d ξ (rootedWeight α₀ γ z) x w).toReal ≤
      (weylScaling d ξ (rootedWeight α₀ γ z) x y).toReal + (weylScaling d ξ (rootedWeight α₀ γ z) y w).toReal
    have h := IsEuclideanLengthMetric.weylScaling_triangle hd ξ (rootedWeight α₀ γ z) x y w
    calc (weylScaling d ξ (rootedWeight α₀ γ z) x w).toReal
        ≤ (weylScaling d ξ (rootedWeight α₀ γ z) x y + weylScaling d ξ (rootedWeight α₀ γ z) y w).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfinW x y, hfinW y w⟩) h
      _ = _ := ENNReal.toReal_add (hfinW x y) (hfinW y w)
  · constructor
    · intro hU p0 hp0
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hU p0 hp0
      obtain ⟨δ, hδ, hδr, c, hc, hcle⟩ := barrier_at hd ξ α₀ γ (fun w => hfinW p0 w) hr
      refine ⟨c, hc, fun w hw => hball ?_⟩
      rw [mem_ball]
      by_contra hcon
      have hw' : (weylScaling d ξ (rootedWeight α₀ γ z) p0 w).toReal < c := hw
      have := hcle w (le_trans hδr (not_lt.1 hcon))
      linarith
    · intro hprop
      refine (hd.isOpen_iff U).2 (fun p0 hp0 => ?_)
      obtain ⟨ε, hε, hsub⟩ := hprop p0 hp0
      have hV : ∀ᶠ w in 𝓝 p0, (weylScaling d ξ (rootedWeight α₀ γ z) p0 w).toReal < ε :=
        (tendsto_order.1 (tendsto_E_all ξ α₀ γ hd hz hW hA hfin p0)).2 ε hε
      obtain ⟨O, hOV, hO, hp0O⟩ := _root_.eventually_nhds_iff.1 hV
      obtain ⟨δ0, hδ0, hball0⟩ := (hd.isOpen_iff O).1 hO p0 hp0O
      exact ⟨δ0, hδ0, fun w hw => hsub w (hOV w (hball0 w hw))⟩
  · exact IsEuclideanLengthMetric.weylScaling_internalMetric hd ξ _
      (E := fun a b => (weylScaling d ξ (rootedWeight α₀ γ z) a b).toReal)
      (fun a b => ENNReal.ofReal_toReal (hfinW a b))
      (fun a b => by
        show (weylScaling d ξ (rootedWeight α₀ γ z) a b).toReal =
          (weylScaling d ξ (rootedWeight α₀ γ z) b a).toReal
        rw [hsymm a b]) x y

end FirstPassS11atProducers
