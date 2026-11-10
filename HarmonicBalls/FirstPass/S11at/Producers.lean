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

end FirstPassS11atProducers
