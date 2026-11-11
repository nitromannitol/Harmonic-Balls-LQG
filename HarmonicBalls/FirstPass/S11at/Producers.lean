import HarmonicBalls.FirstPass.S11r.RootedRootFinite
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.Frozen.S11i
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Proposed.DuplantierMillerSheffield
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.S11u
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleTestFubiniLimit
import HarmonicBalls.Proofs.Sec8.CircleDensityContinuousLimit

/-!
# Producers of `hLen` and `hμ` for the rooted certificate

The rooted insertion weight is
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

/-- **Finiteness of the rooted Weyl scaling on the punctured plane** (`hLen`, Steps 2-3).
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

/-! ### The point `0`: finiteness and continuity (Step 4) -/

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

/-- **Confined comparison at `0`** (Step 4). Let `B` bound `ξ · rootFactor` on `closedBall 0 r` and
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

/-- **Step 4.** At the point `0` the rooted Weyl scaling is finite everywhere and tends to `0`
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

/-! ### Local control at every point (Step 5): annulus barrier and near-geodesic bound -/

/-- **Annulus barrier** (Step 5). If the weight is at least `m` on the annulus `δ' < dist(·, x) < δ`, if the
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

/-- Upper bound for the `d`-length-weighted cost near a point where the weight is bounded above (Step 5,
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

/-- Weight lower bound on an annulus (compactness; Step 5). If `f` is continuous on the closed annulus
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

/-- A radius avoiding the points `a`, `b` other than the centre `x` (Step 5: the annuli stay off the insertions). -/
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

/-- **Generic Euclidean continuity at a point** (Step 5, from the upper bound): if the nonnegative
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

/-- **Barrier at a point** (Step 5, separation and Euclidean openness). For every centre `x` and every
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

/-- **Deterministic `hLen`.** For a Euclidean length metric `d` and a root `z ≠ 0`, the
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

universe u

/-- **`hLen` at a fixed root, almost surely**. For `z ≠ 0`, almost surely the rooted metric of
`rootedWeight α₀ γ z` is a Euclidean length metric. The base metric comes from `LQGMetricLengthUnivFrozen`, the Dα
input (`IsEuclideanLengthMetric` and finiteness) from clause I of `LQGMetricFieldAxiomsUnivFrozen`, and the root continuity
from `RootedPhysicalMetricContinuousAtInsertionFrozen`; the deterministic step is
`rootedWeight_isEuclideanLengthMetric_of_inputs`. -/
theorem rootedWeylMetric_ae_isEuclideanLengthMetric (hLenFr : LQGMetricLengthUnivFrozen.{u})
    (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{u}) (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hP : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) {z : ℂ} (hz : z ≠ 0) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => (weylScaling (𝔇 (hC ω)) ξ (rootedWeight α₀ γ z) x y).toReal) := by
  have hLenAe := hLenFr γ ξ 𝔇 hγ0 hγ2 h𝔇 Ω P hC hcirc hP
  have hFieldAe := (hFieldFr Ω P γ ξ α₀ hC hcirc hP hγ0 hγ2 hα 𝔇 h𝔇).1
  have hRootAe := hRootFr γ ξ α₀ z hγ0 hγ2 hα hz Ω P hC hcirc hP 𝔇 h𝔇
  filter_upwards [hLenAe, hFieldAe, hRootAe] with ω h1 h2 h3
  exact rootedWeight_isEuclideanLengthMetric_of_inputs ξ α₀ γ h1 hz h3 h2.2 (fun a b => (h2.1 a b).ne)

/-- **`hLen`, almost everywhere in the root**: the root `0` is `volume`-null, so the almost sure
statement holds for `volume.restrict S`, for every set `S`. -/
theorem rootedWeylMetric_ae_z (hLenFr : LQGMetricLengthUnivFrozen.{u})
    (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{u}) (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ ξ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hP : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) (S : Set ℂ) :
    ∀ᵐ z ∂(volume.restrict S), ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun x y => (weylScaling (𝔇 (hC ω)) ξ (rootedWeight α₀ γ z) x y).toReal) := by
  have hz0 : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae_restrict_of_ae hz0] with z hz
  exact rootedWeylMetric_ae_isEuclideanLengthMetric hLenFr hFieldFr hRootFr P γ ξ α₀ hC hcirc hP 𝔇 h𝔇 hγ0 hγ2 hα hz

/-! ### hμ: the rooted LQG measure exists for almost every root

Steps 1, 3, 5, 6 and 7 of the §2 derivation are formalized below. The measurable pairing-to-profile map and the
GMC-success set (Steps 2 and 4) and the identification of the DMS-shifted profile (Step 6) have no written argument
in the plan or in the corrected draft; they are kept as the named hypothesis `HMuPairingBridge`. -/

/-- Adding a constant `κ` to the circle-average profile multiplies the approximations by `e^{γκ}`:
`lqgApprox γ (h + κ) ε = e^{γκ} · lqgApprox γ h ε` (Duplantier-Sheffield, eq:measure-lim, Defs/LQG.lean:46). -/
theorem lqgApprox_add_const (γ κ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) :
    lqgApprox γ (fun e x => hε e x + κ) ε = ENNReal.ofReal (Real.exp (γ * κ)) • lqgApprox γ hε ε := by
  unfold lqgApprox
  ext s hs
  rw [withDensity_apply _ hs, Measure.smul_apply, withDensity_apply _ hs, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

/-- Constant-shift scaling of an LQG limit: if `ν` is the γ-LQG limit of `h + κ`, then `e^{-γκ} ν` is the
γ-LQG limit of `h` (the vague-limit statement is preserved under the constant rescaling). -/
theorem isLQGLimit_of_add_const {γ κ : ℝ} {hε : ℝ → ℂ → ℝ} {ν : Measure ℂ}
    (h : IsLQGLimit γ (fun e x => hε e x + κ) ν) :
    IsLQGLimit γ hε (ENNReal.ofReal (Real.exp (-(γ * κ))) • ν) := by
  have hloc : IsLocallyFiniteMeasure (ENNReal.ofReal (Real.exp (-(γ * κ))) • ν) := by
    refine ⟨fun x => ?_⟩
    obtain ⟨s, hs, hfin⟩ := h.isLocallyFiniteMeasure.finiteAtNhds x
    exact ⟨s, hs, by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin⟩
  refine ⟨hloc, fun f hf hc => ?_⟩
  · have hkey : ∀ k : ℕ, ∫ z, f z ∂(lqgApprox γ hε (dyadicScale k)) =
        Real.exp (-(γ * κ)) * ∫ z, f z ∂(lqgApprox γ (fun e x => hε e x + κ) (dyadicScale k)) := by
      intro k
      rw [lqgApprox_add_const, integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul,
        ← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    rw [integral_smul_measure, ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    simp only [hkey]
    exact (h.tendsto_integral f hf hc).const_mul _

/-- The LQG limit depends only on the circle averages at the dyadic radii `dyadicScale k`. -/
theorem isLQGLimit_congr_of_pos {γ : ℝ} {hε hε' : ℝ → ℂ → ℝ} {m : Measure ℂ}
    (heq : ∀ k : ℕ, ∀ z : ℂ, hε (dyadicScale k) z = hε' (dyadicScale k) z)
    (h : IsLQGLimit γ hε m) : IsLQGLimit γ hε' m := by
  have hk : ∀ k : ℕ, lqgApprox γ hε (dyadicScale k) = lqgApprox γ hε' (dyadicScale k) := fun k => by
    unfold lqgApprox
    congr 1
    funext z
    rw [heq k z]
  refine ⟨h.isLocallyFiniteMeasure, fun f hf hc => ?_⟩
  have h1 := h.tendsto_integral f hf hc
  simp only [hk] at h1
  exact h1

/-- The circle-average profile of a continuous profile at a positive radius is the profile itself. -/
theorem circleProfile_eq_of_pos {F : C(CircleParameter, ℝ)} {g : ℝ → ℂ → ℝ}
    (hF : ∀ p : CircleParameter, F p = g p.1 p.2) {r : ℝ} (hr : 0 < r) (z : ℂ) :
    circleProfile F r z = g r z := by
  unfold circleProfile
  simp only [hr, reduceDIte]
  exact hF (⟨r, hr⟩, z)

/-- The `α₀`-inserted GMC-success set of pairing functionals, read through the profile map `G`. -/
noncomputable def HMuGoodSet (γ α₀ : ℝ) (G : ((ℂ → ℝ) → ℝ) → C(CircleParameter, ℝ)) : Set ((ℂ → ℝ) → ℝ) :=
  {T | ∃ ν : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α₀ (circleProfile (G T))) ν}

/-- **Named gap `HMuPairingBridge`**. It asserts the three facts the plan states without argument:
(a) a map `G` from pairing functionals to continuous circle profiles with `G (hC ω) = hcirc ω` almost surely (Step 2;
the repository's measurable version `IsWholePlaneGFF.exists_measurable_continuous_circle_version` is an `Ω`-level map,
not a function of the pairings);
(b) the GMC-success set `HMuGoodSet` of pairings is measurable for the pairing σ-algebra (Step 4);
(c) for `volume`-a.e. root in `ball 0 1` and `P`-a.e. ω, the profile of the DMS-shifted pairing is the circle-average
profile of `h + f_z + κ` (Step 6; `dmsShift`, `dmsConstant` of Proposed/DuplantierMillerSheffield.lean). -/
def HMuPairingBridge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Prop :=
  ∃ G : ((ℂ → ℝ) → ℝ) → C(CircleParameter, ℝ),
    (∀ᵐ ω ∂P, ∀ p : CircleParameter, G (hC ω) p = hcirc ω p.1 p.2) ∧
    MeasurableSet[pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ] (HMuGoodSet γ α₀ G) ∧
    (∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P, ∀ p : CircleParameter,
      G (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) p =
        hcirc ω p.1 p.2 + Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) + dmsConstant γ z (hcirc ω 1 0))

/-- Indicator of the complement of the GMC-success set, as a function of the pairing and the root (the root is
ignored: the marking in `DMSLemmaA10WholePlaneMarked` is trivial here). -/
noncomputable def HMuIndicator (γ α₀ : ℝ) (G : ((ℂ → ℝ) → ℝ) → C(CircleParameter, ℝ)) (q : ((ℂ → ℝ) → ℝ) × ℂ) : ℝ≥0∞ :=
  (HMuGoodSet γ α₀ G)ᶜ.indicator (fun _ => 1) q.1

theorem HMuIndicator_eq_zero_iff (γ α₀ : ℝ) (G : ((ℂ → ℝ) → ℝ) → C(CircleParameter, ℝ))
    (T : (ℂ → ℝ) → ℝ) (z : ℂ) :
    HMuIndicator γ α₀ G (T, z) = 0 ↔ T ∈ HMuGoodSet γ α₀ G := by
  unfold HMuIndicator
  by_cases h : T ∈ HMuGoodSet γ α₀ G <;> simp [h]

/-- The map `(z, ω) ↦ z ↦ x ↦ f_z` in the variable `z`: `dmsShift` is jointly measurable. -/
theorem measurable_dmsShift_joint (γ : ℝ) : Measurable (fun q : ℂ × ℂ => dmsShift γ q.1 q.2) := by
  unfold dmsShift
  exact (measurable_const.mul (Real.measurable_log.comp (measurable_snd.sub measurable_fst).norm)).add
    (measurable_const.mul (Real.measurable_log.comp (measurable_snd.norm.max measurable_const)))

theorem measurable_integral_dmsShift (γ : ℝ) (φ : ℂ → ℝ) (hφ : Measurable φ) :
    Measurable (fun z : ℂ => ∫ w, dmsShift γ z w * φ w) := by
  have hjoint : Measurable (fun q : ℂ × ℂ => dmsShift γ q.1 q.2 * φ q.2) :=
    (measurable_dmsShift_joint γ).mul (hφ.comp measurable_snd)
  exact (hjoint.stronglyMeasurable.integral_prod_right').measurable

set_option maxHeartbeats 400000 in
theorem measurable_circleAverage_dmsShift (γ : ℝ) :
    Measurable (fun z : ℂ => Real.circleAverage (dmsShift γ z) 0 1) := by
  have hcm : Measurable (fun θ : ℝ => circleMap (0 : ℂ) 1 θ) := (continuous_circleMap (0 : ℂ) 1).measurable
  have h1 : Measurable (fun q : ℂ × ℝ => q.1) := measurable_fst
  have h2 : Measurable (fun q : ℂ × ℝ => circleMap (0 : ℂ) 1 q.2) := hcm.comp measurable_snd
  have hjoint : Measurable (fun q : ℂ × ℝ => dmsShift γ q.1 (circleMap (0 : ℂ) 1 q.2)) :=
    (measurable_dmsShift_joint γ).comp (h1.prodMk h2)
  have hint : Measurable (fun z : ℂ =>
      ∫ θ in Set.Ioc 0 (2 * Real.pi), dmsShift γ z (circleMap (0 : ℂ) 1 θ)) :=
    (hjoint.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Ioc 0 (2 * Real.pi)))).measurable
  have heq : (fun z : ℂ => Real.circleAverage (dmsShift γ z) 0 1) =
      fun z => (2 * Real.pi)⁻¹ * ∫ θ in Set.Ioc 0 (2 * Real.pi), dmsShift γ z (circleMap (0 : ℂ) 1 θ) := by
    funext z
    unfold Real.circleAverage
    rw [intervalIntegral.integral_of_le (by positivity), smul_eq_mul]
  rw [heq]
  exact hint.const_mul _

theorem measurable_dmsConstant_joint (γ : ℝ) {X : Type*} [MeasurableSpace X] (g : X → ℝ) (hg : Measurable g) :
    Measurable (fun q : ℂ × X => dmsConstant γ q.1 (g q.2)) := by
  unfold dmsConstant
  exact ((hg.comp measurable_snd).add ((measurable_circleAverage_dmsShift γ).comp measurable_fst)).neg

/-- A map into the pairing σ-algebra is measurable as soon as each test-function evaluation of it is. -/
theorem measurable_into_pairing {X : Type*} [MeasurableSpace X] (F : X → (ℂ → ℝ) → ℝ)
    (hF : ∀ φ : ℂ → ℝ, IsTestFunction Set.univ φ → Measurable fun x => F x φ) :
    @Measurable X ((ℂ → ℝ) → ℝ) _ (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ) F := by
  rw [measurable_iff_comap_le]
  unfold pairingSigmaAlgebra
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun φ hφ => ?_
  exact measurable_iff_comap_le.1 (hF φ hφ)

/-- The DMS-shifted pairing `(z, ω) ↦ dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)` is pairing-measurable. -/
theorem measurable_dmsShiftedPairing {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hh : IsWholePlaneGFF P hC hcirc) :
    @Measurable (ℂ × Ω) ((ℂ → ℝ) → ℝ) _ (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ)
      (fun q => dmsShiftedPairing γ q.1 (hC q.2) (hcirc q.2 1 0)) := by
  refine measurable_into_pairing _ fun φ hφ => ?_
  have hφm : Measurable φ := hφ.1.continuous.measurable
  have h1 : Measurable (fun q : ℂ × Ω => hC q.2 φ) := (hh.measurable_pairing φ hφ).comp measurable_snd
  have h2 : Measurable (fun q : ℂ × Ω => ∫ w, dmsShift γ q.1 w * φ w) :=
    (measurable_integral_dmsShift γ φ hφm).comp measurable_fst
  have hκ : Measurable (fun ω : Ω => hcirc ω 1 0) := hh.measurable_circle 1 0 one_pos
  have h3 : Measurable (fun q : ℂ × Ω => dmsConstant γ q.1 (hcirc q.2 1 0) * ∫ w, φ w) :=
    (measurable_dmsConstant_joint γ (fun ω => hcirc ω 1 0) hκ).mul measurable_const
  exact (h1.add h2).add h3

/-- Definitional copy of `rootedCircleField` (FirstPass/S11at.lean:615). The wrapper file imports this module, so the
producer cannot import it back; the two are equal by unfolding. -/
noncomputable def rootedCircleFieldP {Ω : Type*} (α₀ γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) : Ω → ℝ → ℂ → ℝ :=
  fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω))
    (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))

/-- The rooted circle-average profile of the DMS-shifted field: at a positive radius it is the rooted profile
`rootedCircleField` plus the DMS constant `κ`. -/
theorem circleProfile_shift_eq (α₀ γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ) (κ : ℝ) (F : C(CircleParameter, ℝ))
    (hF : ∀ p : CircleParameter, F p = hcirc p.1 p.2 + Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) + κ)
    {r : ℝ} (hr : 0 < r) (x : ℂ) :
    fieldCircleAverage α₀ (circleProfile F) r x =
      addCircleAverage (fieldCircleAverage α₀ hcirc)
        (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) r x + κ := by
  have hfun : dmsShift γ z = fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖) := by
    funext w
    unfold dmsShift
    rw [max_comm]
  have hF' : circleProfile F r x = hcirc r x + Real.circleAverage (dmsShift γ z) x r + κ :=
    circleProfile_eq_of_pos (g := fun a b => hcirc a b + Real.circleAverage (dmsShift γ z) b a + κ) hF hr x
  unfold fieldCircleAverage addCircleAverage
  rw [hF', hfun]
  ring

/-- **`hμ` producer** (Steps 1, 3, 5, 6 and 7). For a.e. root `z` in `ball c₁ r₁`, the rooted
γ-LQG measure of `rootedCircleFieldP α₀ γ hcirc z` exists almost surely. The argument: the unrooted measure at insertion
`0` (`LQGMeasureExistence`) weights the marked DMS identity `DMSLemmaA10WholePlaneMarked`; the GMC-success indicator
has zero weighted integral, so the DMS-shifted pairing is GMC-good for a.e. root and a.s.; the DMS constant `κ` is
absorbed by the constant rescaling `isLQGLimit_of_add_const`. The measurable profile map and the GMC-success set are
the named gap `HMuPairingBridge`. -/
theorem ae_exists_rootedLQGMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ : ℂ) (r₁ : ℝ)
    (hh : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ)
    (hBridge : HMuPairingBridge P γ α₀ hC hcirc) (hWin : ball c₁ r₁ ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleFieldP α₀ γ hcirc z) μz := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨lam, hlam⟩ := hExist0 hh hγ0 hγ2 hQ
  obtain ⟨μα, hμα⟩ := hExistα hh hγ0 hγ2 hα
  obtain ⟨G, hGae, hGset, hShift⟩ := hBridge
  have hμα' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μα ω) := hμα
  have hGoodAs : ∀ᵐ ω ∂P, hC ω ∈ HMuGoodSet γ α₀ G := by
    filter_upwards [hμα', hGae] with ω h1 h2
    show ∃ ν : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α₀ (circleProfile (G (hC ω)))) ν
    refine ⟨μα ω, isLQGLimit_congr_of_pos (fun k z => ?_) h1⟩
    unfold fieldCircleAverage
    rw [circleProfile_eq_of_pos (g := hcirc ω) h2 (dyadicScale_pos k) z]
  -- the DMS marked identity, applied to the indicator of the complement of the GMC-success set
  have hΨm : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance]
      (HMuIndicator γ α₀ G) :=
    (measurable_const.indicator hGset.compl).comp measurable_fst
  have hDMS := hA10 lam hh hlam (HMuIndicator γ α₀ G) hΨm
  have hL : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, HMuIndicator γ α₀ G (hC ω, z) ∂(lam ω) ∂P = 0 := by
    have h0 : ∀ᵐ ω ∂P, ∫⁻ z in ball (0 : ℂ) 1, HMuIndicator γ α₀ G (hC ω, z) ∂(lam ω) = 0 := by
      filter_upwards [hGoodAs] with ω hω
      have hz : ∀ z : ℂ, HMuIndicator γ α₀ G (hC ω, z) = 0 :=
        fun z => (HMuIndicator_eq_zero_iff γ α₀ G _ z).2 hω
      simp only [hz, lintegral_zero]
    rw [lintegral_congr_ae h0]
    simp
  have hR : ∫⁻ z in ball (0 : ℂ) 1,
      ∫⁻ ω, HMuIndicator γ α₀ G (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume = 0 := by
    rw [← hDMS]
    exact hL
  have hjoint : Measurable (fun q : ℂ × Ω =>
      HMuIndicator γ α₀ G (dmsShiftedPairing γ q.1 (hC q.2) (hcirc q.2 1 0), q.1)) :=
    (measurable_const.indicator hGset.compl).comp (measurable_dmsShiftedPairing P γ hC hcirc hh)
  have hg : Measurable (fun z : ℂ =>
      ∫⁻ ω, HMuIndicator γ α₀ G (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P) :=
    hjoint.lintegral_prod_right'
  have hz0 := (lintegral_eq_zero_iff hg).1 hR
  have hz1 : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P,
      HMuIndicator γ α₀ G (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) = 0 := by
    filter_upwards [hz0] with z hz
    have hzm : Measurable (fun ω : Ω => (z, ω)) := measurable_const.prodMk measurable_id
    exact (lintegral_eq_zero_iff (hjoint.comp hzm)).1 hz
  have hz2 : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P,
      dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) ∈ HMuGoodSet γ α₀ G := by
    filter_upwards [hz1] with z hz
    filter_upwards [hz] with ω hω
    exact (HMuIndicator_eq_zero_iff γ α₀ G _ z).1 hω
  have hall : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P,
      dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) ∈ HMuGoodSet γ α₀ G ∧
        ∀ p : CircleParameter, G (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) p =
          hcirc ω p.1 p.2 + Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) + dmsConstant γ z (hcirc ω 1 0) := by
    filter_upwards [hz2, hShift] with z h1 h2
    filter_upwards [h1, h2] with ω hA hB
    exact ⟨hA, hB⟩
  have hwin := ae_restrict_of_ae_restrict_of_subset hWin hall
  -- the constant rescaling of the DMS-shifted profile gives the rooted measure, pointwise in (z, ω)
  filter_upwards [hwin] with z hz
  have hpt : ∀ ω, ∃ μ : Measure ℂ,
      (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) ∈ HMuGoodSet γ α₀ G ∧
        ∀ p : CircleParameter, G (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) p =
          hcirc ω p.1 p.2 + Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) + dmsConstant γ z (hcirc ω 1 0)) →
        IsLQGLimit γ (rootedCircleFieldP α₀ γ hcirc z ω) μ := by
    intro ω
    by_cases hω : dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) ∈ HMuGoodSet γ α₀ G ∧
        ∀ p : CircleParameter, G (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) p =
          hcirc ω p.1 p.2 + Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) + dmsConstant γ z (hcirc ω 1 0)
    · obtain ⟨hmem, hid⟩ := hω
      obtain ⟨ν, hν⟩ := hmem
      refine ⟨ENNReal.ofReal (Real.exp (-(γ * dmsConstant γ z (hcirc ω 1 0)))) • ν, fun _ => ?_⟩
      apply isLQGLimit_of_add_const (κ := dmsConstant γ z (hcirc ω 1 0))
      apply isLQGLimit_congr_of_pos (fun k x => ?_) hν
      exact circleProfile_shift_eq α₀ γ z (hcirc ω) (dmsConstant γ z (hcirc ω 1 0)) _ hid (dyadicScale_pos k) x
    · exact ⟨0, fun h => absurd h hω⟩
  choose μz hμz using hpt
  refine ⟨μz, ?_⟩
  unfold IsLQGMeasure
  filter_upwards [hz] with ω hω
  exact hμz ω hω

/-- The annular width parameter `η_j = (r/4) (1/2)^j` of the `j`-th explicit approximant. -/
noncomputable def approxEta (r : ℝ) (j : ℕ) : ℝ := (r / 4) * (1 / 2 : ℝ) ^ j

theorem approxEta_pos {r : ℝ} (hr : 0 < r) (j : ℕ) : 0 < approxEta r j := by
  unfold approxEta; positivity

theorem approxEta_le {r : ℝ} (hr : 0 < r) (j : ℕ) : approxEta r j ≤ r / 4 := by
  unfold approxEta
  exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (by norm_num) (by norm_num))

/-- The explicit unit annular approximant `ψ_j` of the circle average at `(r, z)`: the density of
`FirstPass/S11u` with annulus width `r * η_j`. -/
noncomputable def circleApprox {r : ℝ} (hr : 0 < r) (z : ℂ) (j : ℕ) : ℂ → ℝ :=
  unitCircleDensity r (r * approxEta r j) (mul_pos hr (approxEta_pos hr j)) z

theorem integral_circleApprox {r : ℝ} (hr : 0 < r) (z : ℂ) (j : ℕ) :
    ∫ x, circleApprox hr z j x = 1 :=
  integral_unitCircleDensity hr.le (mul_pos hr (approxEta_pos hr j)) z

theorem isTestFunction_circleApprox {r : ℝ} (hr : 0 < r) (z : ℂ) (j : ℕ) :
    IsTestFunction univ (circleApprox hr z j) :=
  isTestFunction_unitCircleDensity z hr (approxEta_pos hr j) (subset_univ _)

/-- **A.s. convergence of the explicit annular approximants** (the argument of
`wholePlaneCircleAverageLimit_derived`, with the explicit geometric widths). -/
theorem ae_tendsto_circleApprox {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (circleApprox hr z j)) atTop (𝓝 (hcirc ω r z)) := by
  have hD : ∀ j, MemLp (fun ω => hC ω (circleApprox hr z j) - hcirc ω r z) 2 P := by
    intro j
    have hp : MemLp (fun ω => hC ω (circleApprox hr z j)) 2 P :=
      (hGFF.isGaussianProcess.hasGaussianLaw_eval
        (⟨.pairing _, isTestFunction_circleApprox hr z j⟩ : GFFObservable.Admissible)).memLp (by simp)
    have hz : MemLp (fun ω => hcirc ω r z) 2 P := (hGFF.hasGaussianLaw_circle hr z).memLp (by simp)
    exact hp.sub hz
  have hbound : ∀ j, ∫ ω, (hC ω (circleApprox hr z j) - hcirc ω r z) ^ 2 ∂P ≤
      8 * (r / 4) / r * (1 / 2) ^ j := by
    intro j
    rw [integral_sq_pairing_sub_circle_eq_variance hGFF hr z _ (isTestFunction_circleApprox hr z j),
      variance_pairing_sub_circle_eq hGFF hr z _ (isTestFunction_circleApprox hr z j)]
    have hηr : approxEta r j ≤ r / 2 := (approxEta_le hr j).trans (by linarith)
    have hc := abs_unitCircleDensity_covariance_combination (r := r) (δ := r * approxEta r j)
      (η := approxEta r j) hr (mul_pos hr (approxEta_pos hr j)) (by linarith [approxEta_le hr j]) le_rfl z
    have hl := log_add_sub_log_sub_le_four_mul hr (approxEta_pos hr j) hηr
    refine le_trans (le_abs_self _) (le_trans hc ?_)
    have hscale : 2 * (4 * approxEta r j / r) = 8 * (r / 4) / r * (1 / 2) ^ j := by
      unfold approxEta
      field_simp
      ring
    linarith
  have hsum : Summable (fun j : ℕ => 8 * (r / 4) / r * (1 / 2 : ℝ) ^ j) :=
    summable_geometric_two.mul_left _
  filter_upwards [ae_tendsto_zero_of_summable_integral_sq
    (fun j ω => hC ω (circleApprox hr z j) - hcirc ω r z) hD _ hsum hbound] with ω hω
  exact tendsto_sub_nhds_zero_iff.mp hω

/-- Continuous observables: the annular averages converge to the circle average, for any widths
`δ_j → 0`. -/
theorem tendsto_unitCircleDensity_mul_continuous {r : ℝ} (hr : 0 < r) {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j, N ≤ j → δ j ≤ r * η) (z : ℂ) {f : ℂ → ℝ}
    (hf : Continuous f) :
    Tendsto (fun j => ∫ x, unitCircleDensity r (δ j) (hδ j) z x * f x) atTop
      (𝓝 (Real.circleAverage f z r)) := by
  have hg : Continuous (Real.circleAverage f z) := by fun_prop
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨κ, hκ, hk⟩ := Metric.continuousAt_iff.mp hg.continuousAt (ε / 2) (half_pos hε)
  set η : ℝ := min κ (r / 2) with hηdef
  have hη : 0 < η := lt_min hκ (by linarith)
  have hηκ : η ≤ κ := min_le_left _ _
  obtain ⟨N, hN⟩ := hsmall η hη
  refine Filter.eventually_atTop.mpr ⟨N, fun j hj => ?_⟩
  have hint := integral_normalized_circleDensity_eq_circleAverage hr.le (hδ j) z hf
  have hb := circleDensityRadialWeight_integral_sub_le hr (hδ j) (hN j hj) (Real.circleAverage f z) hg
    (ε := ε / 2) (by
      intro ρ hρ
      have hd : dist ρ r < κ := by
        rw [Real.dist_eq]
        linarith
      have := hk hd
      rw [Real.dist_eq] at this
      exact this.le)
  have hab := abs_le.mp hb
  unfold unitCircleDensity
  rw [Real.dist_eq, hint, abs_lt]
  constructor <;> linarith [hab.1, hab.2]

/-- Logarithmic observables: `∫ μ_j(x) log ‖x - w‖ → log max(r, ‖z - w‖)` for any widths `δ_j → 0`. -/
theorem tendsto_unitCircleDensity_mul_log {r : ℝ} (hr : 0 < r) {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j, N ≤ j → δ j ≤ r * η) (z w : ℂ) :
    Tendsto (fun j => ∫ x, unitCircleDensity r (δ j) (hδ j) z x * Real.log ‖x - w‖) atTop
      (𝓝 (Real.log (max r ‖z - w‖))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := min (r / 2) (ε * r / 8) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηr : η ≤ r / 2 := min_le_left _ _
  have hηε : η ≤ ε * r / 8 := min_le_right _ _
  obtain ⟨N, hN⟩ := hsmall η hη
  refine Filter.eventually_atTop.mpr ⟨N, fun j hj => ?_⟩
  have hb := abs_circleDensity_log_potential_sub_circle_le hr (hδ j)
    (lt_of_le_of_lt hηr (by linarith)) (hN j hj) z w
  have hl := log_add_sub_log_sub_le_four_mul hr hη hηr
  have h4 : 4 * η / r ≤ ε / 2 := by
    rw [div_le_iff₀ hr]
    nlinarith
  unfold unitCircleDensity
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hb.trans (hl.trans h4)) (by linarith)

/-- DMS-shifted observables: `∫ μ_j(x) f_{z'}(x) → ⨍_{∂B_r(z)} f_{z'}`, the circle average of the DMS shift. -/
theorem tendsto_unitCircleDensity_mul_dmsShift {r : ℝ} (hr : 0 < r) {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j, N ≤ j → δ j ≤ r * η) (γ : ℝ) (z z' : ℂ) :
    Tendsto (fun j => ∫ x, unitCircleDensity r (δ j) (hδ j) z x * dmsShift γ z' x) atTop
      (𝓝 (Real.circleAverage (dmsShift γ z') z r)) := by
  have hlog := tendsto_unitCircleDensity_mul_log hr hδ hsmall z z'
  have hmax := tendsto_unitCircleDensity_mul_continuous hr hδ hsmall z (f := logMaxOne) continuous_logMaxOne
  rw [HarmonicBalls.CircleTestFubini.circleAverage_dmsShift γ z' z hr]
  refine Tendsto.congr (fun j => ?_) ((hlog.const_mul (-γ)).add (hmax.const_mul γ))
  have e : ∀ x, unitCircleDensity r (δ j) (hδ j) z x * dmsShift γ z' x =
      -γ * (unitCircleDensity r (δ j) (hδ j) z x * Real.log ‖x - z'‖) +
        γ * (unitCircleDensity r (δ j) (hδ j) z x * logMaxOne x) := by
    intro x
    unfold dmsShift logMaxOne
    rw [max_comm]
    ring
  have I1 : Integrable (fun x => unitCircleDensity r (δ j) (hδ j) z x * Real.log ‖x - z'‖) :=
    integrable_unitCircleDensity_mul_log hr.le (hδ j) z z'
  have I2 : Integrable (fun x => unitCircleDensity r (δ j) (hδ j) z x * logMaxOne x) :=
    integrable_unitCircleDensity_mul hr.le (hδ j) z continuous_logMaxOne
  simp only [e]
  rw [integral_add (I1.const_mul (-γ)) (I2.const_mul γ), integral_const_mul, integral_const_mul]

namespace FirstPassS11atBridge

instance instNonemptyCircleParameter : Nonempty CircleParameter :=
  ⟨((⟨1, Set.mem_Ioi.2 one_pos⟩ : Set.Ioi (0 : ℝ)), (0 : ℂ))⟩

/-- The dense sequence of circle parameters `p_i` (Mathlib `denseSeq`). -/
noncomputable def denseCircle : ℕ → CircleParameter := TopologicalSpace.denseSeq CircleParameter

theorem denseRange_denseCircle : DenseRange denseCircle := TopologicalSpace.denseRange_denseSeq _

/-- Evaluation of a continuous circle profile on the dense sequence `p_i`. -/
noncomputable def dataMap (y : C(CircleParameter, ℝ)) : ℕ → ℝ := fun i => y (denseCircle i)

theorem continuous_dataMap : Continuous dataMap :=
  continuous_pi fun i => continuous_eval_const (denseCircle i)

/-- A continuous circle profile is determined by its values on the dense sequence `p_i`. -/
theorem dataMap_injective : Function.Injective dataMap := by
  intro y y' h
  have hf : (⇑y) ∘ denseCircle = (⇑y') ∘ denseCircle := funext fun i => congrFun h i
  have heq : (⇑y) = (⇑y') := denseRange_denseCircle.equalizer y.continuous y'.continuous hf
  exact ContinuousMap.ext fun p => congrFun heq p

/-- The image of a measurable set of profiles under the data map is measurable (Lusin-Souslin, since
`C(CircleParameter, ℝ)` is Polish). -/
theorem measurableSet_dataMap_image {s : Set C(CircleParameter, ℝ)} (hs : MeasurableSet s) :
    MeasurableSet (dataMap '' s) :=
  hs.image_of_continuousOn_injOn continuous_dataMap.continuousOn dataMap_injective.injOn

/-- The explicit approximants of the dense circle parameters. -/
noncomputable def approxSeq (i j : ℕ) : ℂ → ℝ :=
  circleApprox (show 0 < (denseCircle i).1.1 from (denseCircle i).1.2) (denseCircle i).2 j

/-- Test-function evaluations are measurable for the pairing σ-algebra. -/
theorem measurable_pairing_eval {Ω : Type*} {hC : Ω → (ℂ → ℝ) → ℝ} {φ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) :
    @Measurable Ω ℝ (pairingSigmaAlgebra hC univ) _ (fun ω => hC ω φ) := by
  refine measurable_iff_comap_le.2 ?_
  unfold pairingSigmaAlgebra
  exact le_iSup₂ (f := fun φ (_ : IsTestFunction univ φ) =>
    MeasurableSpace.comap (fun ω => hC ω φ) inferInstance) φ hφ

/-- The pairing σ-algebra on `Ω` is the pull-back of the pairing σ-algebra on the functional space. -/
theorem pairingSigmaAlgebra_eq_comap {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) :
    pairingSigmaAlgebra hC univ =
      MeasurableSpace.comap hC (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ) := by
  unfold pairingSigmaAlgebra
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]

set_option linter.style.haveILetI false in
/-- Doob-Dynkin factorization through the pairing: a pairing-measurable map into a standard Borel space
factors through the raw pairing. -/
theorem exists_pairing_factor {Ω : Type*} {hC : Ω → (ℂ → ℝ) → ℝ} {Y : Type*} [MeasurableSpace Y]
    [StandardBorelSpace Y] [Nonempty Y] (D : Ω → Y)
    (hD : @Measurable Ω Y (pairingSigmaAlgebra hC univ) _ D) :
    ∃ Φ' : ((ℂ → ℝ) → ℝ) → Y,
      @Measurable ((ℂ → ℝ) → ℝ) Y (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ) _ Φ' ∧
        D = Φ' ∘ hC := by
  letI : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ
  rw [pairingSigmaAlgebra_eq_comap] at hD
  exact hD.exists_eq_measurable_comp

/-- The explicit limit data of a pairing functional along the approximants `approxSeq i`. -/
noncomputable def pairingData {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ω : Ω) : ℕ → ℝ :=
  fun i => limsup (fun j => hC ω (approxSeq i j)) atTop

set_option linter.style.haveILetI false in
/-- The data map is pairing-measurable. -/
theorem measurable_pairingData {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) :
    @Measurable Ω (ℕ → ℝ) (pairingSigmaAlgebra hC univ) _ (pairingData hC) := by
  letI : MeasurableSpace Ω := pairingSigmaAlgebra hC univ
  refine Measurable.of_eval fun i => ?_
  unfold pairingData
  exact Measurable.limsup fun j => measurable_pairing_eval (isTestFunction_circleApprox _ _ j)

/-- The data of the GFF circle averages equals the evaluation of their continuous version, almost surely. -/
theorem ae_pairingData_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {F : Ω → C(CircleParameter, ℝ)}
    (hFcoord : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, pairingData hC ω = dataMap (F ω) := by
  have key : ∀ᵐ ω ∂P, ∀ i : ℕ, pairingData hC ω i = dataMap (F ω) i := by
    refine ae_all_iff.2 fun i : ℕ => ?_
    have hT := ae_tendsto_circleApprox hh (show 0 < (denseCircle i).1.1 from (denseCircle i).1.2)
      (denseCircle i).2
    filter_upwards [hT, hFcoord (denseCircle i)] with ω h1 h2
    unfold pairingData dataMap
    have h1' : Tendsto (fun j => hC ω (approxSeq i j)) atTop
        (𝓝 (hcirc ω (denseCircle i).1 (denseCircle i).2)) := h1
    rw [h1'.limsup_eq]
    exact h2.symm
  filter_upwards [key] with ω hω
  exact funext hω

/-- A measurable conull subset of a set that is conull for the image measure. -/
theorem exists_measurable_conull_subset' {X : Type*} [MeasurableSpace X] (μ : Measure X) (S : Set X)
    (hS : ∀ᵐ x ∂μ, x ∈ S) :
    ∃ A : Set X, MeasurableSet A ∧ (∀ᵐ x ∂μ, x ∈ A) ∧ A ⊆ S := by
  obtain ⟨N, hSN, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hS)
  refine ⟨Nᶜ, hNm.compl, ?_, ?_⟩
  · exact ae_iff.2 (by simpa using hN0)
  · intro x hx
    by_contra hxS
    exact hx (hSN hxS)

/-- **Clauses 1 and 2 of the pairing bridge, derived** (no new frozen input; the decoder input is `hProf`).
There is a pairing-measurable data map `Φ'` (Doob-Dynkin factor of the explicit limit data) and a measurable
set `A` of data, almost surely containing the data of the GFF, every point of which is the data of a continuous
profile with an LQG limit. -/
theorem exists_pairing_good {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (γ α₀ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (μα : Ω → Measure ℂ) (hμα : IsLQGMeasureOfField P γ α₀ hcirc μα)
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{u}) :
    ∃ Φ' : ((ℂ → ℝ) → ℝ) → (ℕ → ℝ),
      @Measurable ((ℂ → ℝ) → ℝ) (ℕ → ℝ) (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ) _ Φ' ∧
      (∀ᵐ ω ∂P, ∀ i : ℕ, Tendsto (fun j => hC ω (approxSeq i j)) atTop (𝓝 (Φ' (hC ω) i))) ∧
      ∃ A : Set (ℕ → ℝ), MeasurableSet A ∧ (∀ᵐ ω ∂P, Φ' (hC ω) ∈ A) ∧
        ∀ x ∈ A, ∃ y : C(CircleParameter, ℝ), dataMap y = x ∧
          ∃ ν : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α₀ (circleProfile y)) ν := by
  obtain ⟨F, hFm, _, hFcoord⟩ := hh.exists_measurable_continuous_circle_version
  obtain ⟨Φ', hΦm, hΦeq⟩ := exists_pairing_factor (pairingData hC) (measurable_pairingData hC)
  obtain ⟨Dec, _, _, hDecGood⟩ := hProf Ω P γ α₀ hC hcirc μα F hh hμα hFm hFcoord
  have hS : ∀ᵐ y ∂(P.map F), y ∈ {y : C(CircleParameter, ℝ) |
      ∃ ν : Measure ℂ, IsLQGLimit γ (fieldCircleAverage α₀ (circleProfile y)) ν} := by
    filter_upwards [hDecGood] with y hy
    exact ⟨Dec y, hy⟩
  obtain ⟨AC, hACm, hACae, hACsub⟩ := exists_measurable_conull_subset' (P.map F) _ hS
  have hΦdata : ∀ᵐ ω ∂P, ∀ i : ℕ, Φ' (hC ω) i = dataMap (F ω) i := by
    filter_upwards [ae_pairingData_eq hh hFcoord] with ω h1 i
    have h3 : Φ' (hC ω) = pairingData hC ω := (congrFun hΦeq ω).symm
    rw [h3, h1]
  refine ⟨Φ', hΦm, ?_, dataMap '' AC, measurableSet_dataMap_image hACm, ?_, ?_⟩
  · refine (ae_all_iff.2 fun i : ℕ => ?_)
    filter_upwards [hΦdata, ae_tendsto_circleApprox hh (show 0 < (denseCircle i).1.1 from (denseCircle i).1.2)
      (denseCircle i).2, hFcoord (denseCircle i)] with ω h1 h2 h3
    rw [h1 i]
    unfold dataMap
    rw [h3]
    exact h2
  · have hFAC : ∀ᵐ ω ∂P, F ω ∈ AC := (ae_map_iff hFm.aemeasurable hACm).1 hACae
    filter_upwards [hΦdata, hFAC] with ω h1 h2
    rw [funext h1]
    exact ⟨F ω, h2, rfl⟩
  · intro x hx
    obtain ⟨y, hyA, rfl⟩ := hx
    obtain ⟨ν, hν⟩ := hACsub hyA
    exact ⟨y, rfl, ν, hν⟩


/-- The explicit annular widths `c * approxEta c j` tend to zero. -/
theorem approxWidth_small {c : ℝ} (hc : 0 < c) :
    ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j, N ≤ j → c * approxEta c j ≤ c * η := by
  intro η hη
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < 4 * η / c by positivity) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨N, fun j hj => ?_⟩
  have h1 : (1 / 2 : ℝ) ^ j ≤ (1 / 2) ^ N := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
  have h2 : (1 / 2 : ℝ) ^ j * c < 4 * η := by
    have h3 : (1 / 2 : ℝ) ^ j < 4 * η / c := lt_of_le_of_lt h1 hN
    rwa [lt_div_iff₀ hc] at h3
  have h4 : approxEta c j ≤ η := by
    unfold approxEta
    nlinarith
  exact mul_le_mul_of_nonneg_left h4 hc.le

/-- Deterministic step: the DMS-shifted pairing tested against the explicit approximants converges to the
limit of the unshifted pairing plus the circle average of the DMS shift plus the constant. -/
theorem tendsto_dmsShiftedPairing_approx (γ : ℝ) (zr : ℂ) (T : (ℂ → ℝ) → ℝ) (h10 : ℝ) {c : ℝ} (hc : 0 < c)
    (z0 : ℂ) {a : ℝ} (h : Tendsto (fun j => T (circleApprox hc z0 j)) atTop (𝓝 a)) :
    Tendsto (fun j => dmsShiftedPairing γ zr T h10 (circleApprox hc z0 j)) atTop
      (𝓝 (a + Real.circleAverage (dmsShift γ zr) z0 c + dmsConstant γ zr h10)) := by
  have h2 := tendsto_unitCircleDensity_mul_dmsShift hc (δ := fun j => c * approxEta c j)
    (hδ := fun j => mul_pos hc (approxEta_pos hc j)) (approxWidth_small hc) γ z0 zr
  have h2' : Tendsto (fun j => ∫ w, dmsShift γ zr w * circleApprox hc z0 j w) atTop
      (𝓝 (Real.circleAverage (dmsShift γ zr) z0 c)) := by
    refine h2.congr (fun j => ?_)
    congr 1
    ext x
    unfold circleApprox
    ring
  have h3 := (h.add h2').add (tendsto_const_nhds (x := dmsConstant γ zr h10))
  refine h3.congr (fun j => ?_)
  unfold dmsShiftedPairing
  rw [integral_circleApprox, mul_one]

set_option linter.style.haveILetI false in
/-- The fibres of the explicit limit data: `{T | T(ψ_{i,j}) → Φ' T i}` is pairing-measurable. -/
theorem measurableSet_codeFiber (Φ' : ((ℂ → ℝ) → ℝ) → (ℕ → ℝ))
    (hΦ : @Measurable ((ℂ → ℝ) → ℝ) (ℕ → ℝ) (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ) _ Φ')
    (i : ℕ) :
    @MeasurableSet ((ℂ → ℝ) → ℝ) (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ)
      {T | Tendsto (fun j => T (approxSeq i j)) atTop (𝓝 (Φ' T i))} := by
  letI : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ
  have hm : Measurable (fun T : (ℂ → ℝ) → ℝ => Φ' T i) := (measurable_pi_apply i).comp hΦ
  have hf : ∀ j : ℕ, Measurable (fun T : (ℂ → ℝ) → ℝ => T (approxSeq i j) - Φ' T i) := fun j =>
    (measurable_pairing_eval (hC := fun T : (ℂ → ℝ) → ℝ => T)
      (isTestFunction_circleApprox _ _ j)).sub hm
  have hset : {T : (ℂ → ℝ) → ℝ | Tendsto (fun j => T (approxSeq i j)) atTop (𝓝 (Φ' T i))} =
      {T | Tendsto (fun j => T (approxSeq i j) - Φ' T i) atTop (𝓝 0)} := by
    ext T
    exact tendsto_sub_nhds_zero_iff.symm
  rw [hset]
  exact measurableSet_tendsto (𝓝 (0 : ℝ)) hf

/-- The DMS-shifted profile of a continuous GFF circle profile is continuous on `CircleParameter`. -/
theorem continuous_dmsProfile (γ : ℝ) (z : ℂ) (hcirc : ℝ → ℂ → ℝ)
    (hcont : ContinuousOn (fun p : ℝ × ℂ => hcirc p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ)) (κ : ℝ) :
    Continuous (fun p : CircleParameter => hcirc p.1 p.2 +
      Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) + κ) := by
  have hcircC : Continuous (fun p : CircleParameter => hcirc p.1 p.2) :=
    continuousOn_univ.mp (hcont.comp (continuous_subtype_val.prodMap continuous_id).continuousOn
      (fun p _ => ⟨p.1.2, Set.mem_univ _⟩))
  have e : ∀ p : CircleParameter, Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) =
      -γ * Real.log (max (p.1 : ℝ) ‖p.2 - z‖) + γ * Real.circleAverage logMaxOne p.2 (p.1 : ℝ) :=
    fun p => HarmonicBalls.CircleTestFubini.circleAverage_dmsShift γ z p.2 p.1.2
  have hmax : Continuous (fun p : CircleParameter => max (p.1 : ℝ) ‖p.2 - z‖) :=
    (continuous_subtype_val.comp continuous_fst).max ((continuous_snd.sub continuous_const).norm)
  have hlog : Continuous (fun p : CircleParameter => Real.log (max (p.1 : ℝ) ‖p.2 - z‖)) :=
    hmax.log fun p => (lt_of_lt_of_le p.1.2 (le_max_left _ _)).ne'
  have hav : Continuous (fun p : CircleParameter => Real.circleAverage logMaxOne p.2 (p.1 : ℝ)) :=
    continuous_circleAverage_logMaxOne.comp (continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst))
  have hshift : Continuous (fun p : CircleParameter => Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ)) := by
    have hfun : (fun p : CircleParameter => Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ)) =
        fun p => -γ * Real.log (max (p.1 : ℝ) ‖p.2 - z‖) + γ * Real.circleAverage logMaxOne p.2 (p.1 : ℝ) :=
      funext e
    rw [hfun]
    exact (continuous_const.mul hlog).add (continuous_const.mul hav)
  exact (hcircC.add hshift).add continuous_const

end FirstPassS11atBridge

open FirstPassS11atBridge

/-- **hμ producer, derived** (no `HMuPairingBridge`; the decoder input is `hProf`). For a.e. root `z` in
`ball c₁ r₁`, the rooted γ-LQG measure of `rootedCircleFieldP α₀ γ hcirc z` exists almost surely. -/
theorem ae_exists_rootedLQGMeasure_derived {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ : ℂ) (r₁ : ℝ)
    (hh : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ)
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{u}) (hWin : ball c₁ r₁ ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleFieldP α₀ γ hcirc z) μz := by
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨lam, hlam⟩ := hExist0 hh hγ0 hγ2 hQ
  obtain ⟨μα, hμα⟩ := hExistα hh hγ0 hγ2 hα
  obtain ⟨Φ', hΦm, hTend, A, hA, hAgood, hAsound⟩ := exists_pairing_good γ α₀ hh μα hμα hProf
  set Code : Set ((ℂ → ℝ) → ℝ) :=
    {T | ∀ i : ℕ, Tendsto (fun j => T (approxSeq i j)) atTop (𝓝 (Φ' T i))} with hCode
  have hCodem : @MeasurableSet ((ℂ → ℝ) → ℝ) (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ) Code := by
    have hset : Code = ⋂ i : ℕ, {T | Tendsto (fun j => T (approxSeq i j)) atTop (𝓝 (Φ' T i))} := by
      ext T
      simp [hCode]
    rw [hset]
    exact MeasurableSet.iInter fun i => measurableSet_codeFiber Φ' hΦm i
  have hGCm : @MeasurableSet ((ℂ → ℝ) → ℝ) (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ)
      (Φ' ⁻¹' A ∩ Code) := (hΦm hA).inter hCodem
  have hCodeAe : ∀ᵐ ω ∂P, hC ω ∈ Code := by
    filter_upwards [hTend] with ω hω
    exact hω
  have hGCae : ∀ᵐ ω ∂P, hC ω ∈ Φ' ⁻¹' A ∩ Code := hAgood.and hCodeAe
  -- the DMS marked identity for the indicator of the complement of `Good ∩ Code`
  have hΨm : Measurable[(pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) univ).prod inferInstance]
      (fun q : ((ℂ → ℝ) → ℝ) × ℂ => (Φ' ⁻¹' A ∩ Code)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) q.1) :=
    (measurable_const.indicator hGCm.compl).comp measurable_fst
  have hDMS := hA10 lam hh hlam _ hΨm
  have hL : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1,
      (Φ' ⁻¹' A ∩ Code)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω) ∂(lam ω) ∂P = 0 := by
    have h0 : ∀ᵐ ω ∂P, ∫⁻ z in ball (0 : ℂ) 1,
        (Φ' ⁻¹' A ∩ Code)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (hC ω) ∂(lam ω) = 0 := by
      filter_upwards [hGCae] with ω hω
      simp [hω]
    rw [lintegral_congr_ae h0]
    simp
  have hR := hDMS.symm.trans hL
  have hjoint : Measurable (fun q : ℂ × Ω =>
      (Φ' ⁻¹' A ∩ Code)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (dmsShiftedPairing γ q.1 (hC q.2) (hcirc q.2 1 0))) :=
    (measurable_const.indicator hGCm.compl).comp (measurable_dmsShiftedPairing P γ hC hcirc hh)
  have hg : Measurable (fun z : ℂ => ∫⁻ ω,
      (Φ' ⁻¹' A ∩ Code)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) ∂P) :=
    hjoint.lintegral_prod_right'
  have hz0 := (lintegral_eq_zero_iff hg).1 hR
  have hz1 : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P,
      (Φ' ⁻¹' A ∩ Code)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) = 0 := by
    filter_upwards [hz0] with z hz
    have hzm : Measurable (fun ω : Ω => (z, ω)) := measurable_const.prodMk measurable_id
    exact (lintegral_eq_zero_iff (hjoint.comp hzm)).1 hz
  have hall : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P,
      dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) ∈ Φ' ⁻¹' A ∩ Code := by
    filter_upwards [hz1] with z hz
    filter_upwards [hz] with ω hω
    by_contra h
    simp [Set.indicator_of_mem (Set.mem_compl h)] at hω
  have hHCae : ∀ᵐ ω ∂P, ∀ i : ℕ,
      Tendsto (fun j => hC ω (approxSeq i j)) atTop (𝓝 (hcirc ω (denseCircle i).1 (denseCircle i).2)) := by
    refine ae_all_iff.2 fun i : ℕ => ?_
    filter_upwards [ae_tendsto_circleApprox hh (show 0 < (denseCircle i).1.1 from (denseCircle i).1.2)
      (denseCircle i).2] with ω h
    exact h
  have hcontAe := hh.ae_continuousOn_circle
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hWin hall] with z hz
  have hpt : ∀ ω, ∃ μ : Measure ℂ,
      (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) ∈ Φ' ⁻¹' A ∩ Code ∧
        ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) ∧
        ∀ i : ℕ, Tendsto (fun j => hC ω (approxSeq i j)) atTop
          (𝓝 (hcirc ω (denseCircle i).1 (denseCircle i).2))) →
      IsLQGLimit γ (rootedCircleFieldP α₀ γ hcirc z ω) μ := by
    intro ω
    by_cases hω : dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0) ∈ Φ' ⁻¹' A ∩ Code ∧
        ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Set.Ioi 0 ×ˢ Set.univ) ∧
        ∀ i : ℕ, Tendsto (fun j => hC ω (approxSeq i j)) atTop
          (𝓝 (hcirc ω (denseCircle i).1 (denseCircle i).2))
    · obtain ⟨hmem, hcont, hHC⟩ := hω
      have hlim : ∀ i : ℕ, Φ' (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) i =
          hcirc ω (denseCircle i).1 (denseCircle i).2 +
            Real.circleAverage (dmsShift γ z) (denseCircle i).2 (denseCircle i).1 +
            dmsConstant γ z (hcirc ω 1 0) := fun i =>
        tendsto_nhds_unique (hmem.2 i)
          (tendsto_dmsShiftedPairing_approx γ z (hC ω) (hcirc ω 1 0) (denseCircle i).1.2 (denseCircle i).2
            (hHC i))
      let prof : C(CircleParameter, ℝ) := ⟨fun p => hcirc ω p.1 p.2 +
          Real.circleAverage (dmsShift γ z) p.2 (p.1 : ℝ) + dmsConstant γ z (hcirc ω 1 0),
        continuous_dmsProfile γ z (hcirc ω) hcont (dmsConstant γ z (hcirc ω 1 0))⟩
      have hdata : dataMap prof = Φ' (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0)) := by
        funext i
        rw [hlim i]
        rfl
      obtain ⟨y, hy, ν, hν⟩ := hAsound _ hmem.1
      have hyprof : y = prof := dataMap_injective (hy.trans hdata.symm)
      rw [hyprof] at hν
      refine ⟨ENNReal.ofReal (Real.exp (-(γ * dmsConstant γ z (hcirc ω 1 0)))) • ν, fun _ => ?_⟩
      apply isLQGLimit_of_add_const (κ := dmsConstant γ z (hcirc ω 1 0))
      apply isLQGLimit_congr_of_pos (fun k x => ?_) hν
      exact circleProfile_shift_eq α₀ γ z (hcirc ω) (dmsConstant γ z (hcirc ω 1 0)) prof (fun p => rfl)
        (dyadicScale_pos k) x
    · exact ⟨0, fun h => absurd h hω⟩
  choose μz hμz using hpt
  refine ⟨μz, ?_⟩
  unfold IsLQGMeasure
  filter_upwards [hz, hcontAe, hHCae] with ω h1 h2 h3
  exact hμz ω ⟨h1, h2, h3⟩

end FirstPassS11atProducers
