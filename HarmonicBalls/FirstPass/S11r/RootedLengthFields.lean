import HarmonicBalls.FirstPass.S11r.RootedRootFinite
import HarmonicBalls.Steps.Sec11.MetricArcLength

/-!
# First pass, length-metric fields of the rooted internal physical metric (fp-S11r-11-13-rooted-length-fields, n2)

Fields for the rooted decoder metric of n4 (`IsLengthMetricOn B D`, `FirstPass/S11ah/LengthTransport.lean:25`) on an open
connected `D`, for the Weyl-scaled physical metric `e = weylPhysicalE d ξ f` of an `IsEuclideanLengthMetric` `d`
(internal metric `I = internalPhysicalMetric e D`):

* `self_eq_zero`: `I x x = 0` on `D` (constant path, `weylPhysicalE_self`);
* `symm`, `triangle`, `ofReal_eq_internalMetric`: from `weylPhysicalE_internalPhysical_props_root`;
* `continuousOn`: `ContinuousOn (fun q => I q.1 q.2) (D ×ˢ D)`. At a point `x ∈ D` with `f` continuous at `x` the one-variable
  statement `I · x → 0` is proved here by the arclength argument of `internalMetric_le_weylScaling_eventually`
  (RootedRootContinuity.lean), with the weight bounded near `x` instead of the root hypothesis; at the root `z` it is
  `internalPhysicalMetric_tendsto_root` (he_cont). The joint continuity follows from the triangle inequality.

Not here: `eq_of_eq_zero` (non-degeneracy) and `isOpen_iff` (Euclidean topology); both wait for ChatGPT chat 192
(notes/fp-gaps/CHATGPT-n4-rooted-length.md).
-/

namespace HarmonicBalls

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal

/-- A length metric is nonnegative: `d x y ≤ d x x + ...`, from `d x x = 0`, symmetry and the triangle inequality. -/
theorem isEuclideanLengthMetric_nonneg {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (x y : ℂ) :
    0 ≤ d x y := by
  have h := hd.triangle x y x
  rw [hd.self_eq_zero, hd.symm y x] at h
  linarith

/-- `d(x, ·) → 0` at `x` within `D` (the length metric tends to `0` at its base point). -/
theorem isEuclideanLengthMetric_tendsto_nhdsWithin {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (x : ℂ)
    (D : Set ℂ) : Tendsto (fun y => d x y) (𝓝[D] x) (𝓝 0) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds ?_
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr, hball⟩ := exists_ball_of_dist_lt hd hε
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (isEuclideanLengthMetric_nonneg hd x y)]
  exact hball y (mem_ball.1 hy)

/-- A length-parametrized path from `x` to `y` of `D`-length below `D x y + ε`: the `D`-length of a near-minimal path in `ℂ`
(`ofReal (D x y) = internalMetric D univ x y`) is arclength-reparametrized (`MetricArcLength.lean`). -/
theorem exists_lengthParametrized_lt {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (x y : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∃ q : ℝ → ℂ, IsLengthParametrized d q T ∧ q 0 = x ∧ q T = y ∧ T < d x y + ε := by
  have hnn : 0 ≤ d x y := by
    have h := hd.triangle x y x
    rw [hd.self_eq_zero, hd.symm y x] at h
    linarith
  have hlt : internalMetric d univ x y < ENNReal.ofReal (d x y + ε) := by
    rw [← hd.ofReal_eq_internalMetric x y]
    exact (ENNReal.ofReal_lt_ofReal_iff' ).2 ⟨by linarith, by linarith⟩
  unfold internalMetric at hlt
  simp only [iInf_lt_iff] at hlt
  obtain ⟨P, -, hP⟩ := hlt
  have hfin : curveLength d P.extend 0 1 < ⊤ := lt_trans hP ENNReal.ofReal_lt_top
  obtain ⟨q, hq, hq0, hqT⟩ :=
    hd.exists_lengthParametrized_of_curveLength_lt_top (T := 1) zero_le_one P.continuous_extend.continuousOn hfin
  refine ⟨_, q, hq, hq0.trans P.extend_zero, hqT.trans P.extend_one, ?_⟩
  exact ENNReal.toReal_lt_of_lt_ofReal hP

/-- The internal metric of a function vanishing on the diagonal vanishes on the diagonal of a set containing the point:
the constant path is admissible and has zero length. -/
theorem internalMetric_self_eq_zero_of_diag {E : ℂ → ℂ → ℝ} (hE : ∀ x, E x x = 0) (D : Set ℂ) {x : ℂ} (hx : x ∈ D) :
    internalMetric E D x x = 0 := by
  have hP : ∀ t, (Path.refl x) t ∈ D := fun t => by simpa using hx
  have h1 : internalMetric E D x x ≤ pathLength E (Path.refl x) := iInf₂_le (Path.refl x) hP
  have h2 : pathLength E (Path.refl x) ≤ 0 := by
    unfold pathLength curveLength
    refine iSup_le fun q => ?_
    simp [hE]
  exact le_antisymm (h1.trans h2) zero_le

/-- **Self-distance of the internal physical metric** (field `self_eq_zero` of `IsLengthMetricOn`). -/
theorem internalPhysicalMetric_self_eq_zero {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (f : ℂ → ℝ)
    (D : Set ℂ) {x : ℂ} (hx : x ∈ D) :
    internalPhysicalMetric (weylPhysicalE d ξ f) D x x = 0 := by
  unfold internalPhysicalMetric
  rw [internalMetric_self_eq_zero_of_diag (weylPhysicalE_self hd ξ f) D hx]
  simp

/-- **One-variable continuity at a point where the weight is continuous** (the non-root case of the continuity field).
If `f` is continuous at `x ∈ D`, then `I(y, x) → 0` as `y → x` within `D`. Proof: for `y` near `x`, an arclength-parametrized
path `q` from `x` to `y` of length `T < d(x,y) + ε` stays in a Euclidean ball around `x` where `exp(ξ f) ≤ M`
(`dist_root_abs_le`, `exists_dist_lt_of_ball`), so `I(x,y) ≤ ∫ exp(ξ f(q t)) dt ≤ M T` by `curveLength_le_weyl_cost`
and the path comparison `internalMetric ≤ pathLength`; then squeeze. -/
theorem internalPhysicalMetric_tendsto_of_continuousAt {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ)
    {f : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) {x : ℂ} (hx : x ∈ D) (hf : ContinuousAt f x) :
    Tendsto (fun y => internalPhysicalMetric (weylPhysicalE d ξ f) D y x) (𝓝[D] x) (𝓝 0) := by
  unfold internalPhysicalMetric
  have hg : ContinuousAt (fun w => Real.exp (ξ * f w)) x :=
    Real.continuous_exp.continuousAt.comp (continuousAt_const.mul hf)
  have hDev : ∀ᶠ w in 𝓝 x, w ∈ D := hD.mem_nhds hx
  have hev : ∀ᶠ w in 𝓝 x, w ∈ D ∧ Real.exp (ξ * f w) < Real.exp (ξ * f x) + 1 :=
    hDev.and (hg.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set M := Real.exp (ξ * f x) + 1 with hMdef
  have hMpos : 0 < M := by positivity
  obtain ⟨c, hc, hcball⟩ := exists_dist_lt_of_ball (z := x) hd hρ
  -- the bound on `I(x, y)` for `y` with `d(x,y) + ε < c`
  have hbound : ∀ y : ℂ, ∀ ε : ℝ, 0 < ε → d x y + ε < c →
      (internalMetric (weylPhysicalE d ξ f) D x y).toReal ≤ M * (d x y + ε) := by
    intro y ε hε hdε
    obtain ⟨T, q, hq, hq0, hqT, hTlt⟩ := exists_lengthParametrized_lt hd x y hε
    have hT0 : 0 ≤ T := hq.1
    have hqc : ∀ t ∈ Icc 0 T, q t ∈ ball x ρ := by
      intro t ht
      apply hcball
      have h1 := dist_root_abs_le hd hq (z := x) (s := 0) (t := t) ⟨le_rfl, hT0⟩ ht
      rw [hq0, hd.self_eq_zero] at h1
      have h2 := (abs_le.1 h1).2
      rw [sub_zero, sub_zero, abs_of_nonneg ht.1] at h2
      linarith [ht.2]
    have hqD : ∀ t ∈ Icc 0 T, q t ∈ D ∧ Real.exp (ξ * f (q t)) < M := fun t ht =>
      hball (mem_ball.1 (hqc t ht))
    obtain ⟨P, hPt, hPle⟩ := exists_path_range_le (E := weylPhysicalE d ξ f) hT0 hq.2.1
    have hPD : ∀ t, P t ∈ D := by
      intro t
      rw [hPt t]
      exact (hqD _ ⟨mul_nonneg hT0 t.2.1, mul_le_of_le_one_right hT0 t.2.2⟩).1
    have hIP : internalMetric (weylPhysicalE d ξ f) D (q 0) (q T) ≤ pathLength (weylPhysicalE d ξ f) P :=
      iInf₂_le P hPD
    have hcurve := curveLength_le_weyl_cost hd ξ f (fun x y => ENNReal.ofReal_toReal_le)
      (fun x y => weylPhysicalE_symm hd ξ f x y) hq
    have hint : ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (q t))) ≤ ENNReal.ofReal (M * T) := by
      calc ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (q t)))
          ≤ ∫⁻ _ in Icc 0 T, ENNReal.ofReal M :=
            setLIntegral_mono' measurableSet_Icc (fun t ht => ENNReal.ofReal_le_ofReal (hqD t ht).2.le)
        _ = ENNReal.ofReal M * volume (Icc 0 T) := setLIntegral_const _ _
        _ = ENNReal.ofReal (M * T) := by rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_mul hMpos.le]
    have hI : internalMetric (weylPhysicalE d ξ f) D x y ≤ ENNReal.ofReal (M * T) := by
      calc internalMetric (weylPhysicalE d ξ f) D x y
          = internalMetric (weylPhysicalE d ξ f) D (q 0) (q T) := by rw [hq0, hqT]
        _ ≤ pathLength (weylPhysicalE d ξ f) P := hIP
        _ ≤ curveLength (weylPhysicalE d ξ f) q 0 T := hPle
        _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (q t))) := hcurve
        _ ≤ ENNReal.ofReal (M * T) := hint
    have hreal : (internalMetric (weylPhysicalE d ξ f) D x y).toReal ≤ M * T :=
      ENNReal.toReal_le_of_le_ofReal (mul_nonneg hMpos.le hT0) hI
    exact hreal.trans (mul_le_mul_of_nonneg_left hTlt.le hMpos.le)
  have hdt : Tendsto (fun y => d x y) (𝓝[D] x) (𝓝 0) := isEuclideanLengthMetric_tendsto_nhdsWithin hd x D
  have hsymI : ∀ a b : ℂ, internalPhysicalMetric (weylPhysicalE d ξ f) D a b =
      internalPhysicalMetric (weylPhysicalE d ξ f) D b a :=
    internalPhysicalMetric_symm_of (internalMetric_symm_of_symm (weylPhysicalE_symm hd ξ f) D)
  refine Tendsto.congr (fun y => hsymI x y) ?_
  unfold internalPhysicalMetric
  refine tendsto_order.2 ⟨fun a ha => Eventually.of_forall fun y => lt_of_lt_of_le ha ENNReal.toReal_nonneg, fun b hb => ?_⟩
  set δ := min (b / (2 * M)) (c / 2) with hδdef
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ b / (2 * M) := min_le_left _ _
  have hδ2 : δ ≤ c / 2 := min_le_right _ _
  filter_upwards [hdt.eventually (gt_mem_nhds hδpos)] with y hy
  have h := hbound y δ hδpos (by linarith)
  have h3 : M * (2 * δ) ≤ M * (2 * (b / (2 * M))) := mul_le_mul_of_nonneg_left (by linarith) hMpos.le
  have h4 : M * (2 * (b / (2 * M))) = b := by field_simp
  have h5 : M * (d x y + δ) < M * (2 * δ) := mul_lt_mul_of_pos_left (by linarith) hMpos
  linarith

/-- **Joint continuity of the internal physical metric on `D × D`** (field `continuousOn` of `IsLengthMetricOn`).
At the root `z` the one-variable limit is `internalPhysicalMetric_tendsto_root` (he_cont, needs `hW`); at `x ≠ z` it is
`internalPhysicalMetric_tendsto_of_continuousAt` (`f` continuous on the open set `D ∖ {z}`). The joint limit follows from
`|I(a,b) - I(x,y)| ≤ I(a,x) + I(b,y)`, which is the triangle inequality with symmetry. -/
theorem internalPhysicalMetric_continuousOn_root {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ)
    {f : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {z : ℂ} (hz : z ∈ D)
    (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    ContinuousOn (fun q : ℂ × ℂ => internalPhysicalMetric (weylPhysicalE d ξ f) D q.1 q.2) (D ×ˢ D) := by
  obtain ⟨hsym, htri, -⟩ := weylPhysicalE_internalPhysical_props_root hd ξ hD hDc hz hfc hW
  have hlim : ∀ x ∈ D, Tendsto (fun y => internalPhysicalMetric (weylPhysicalE d ξ f) D y x) (𝓝[D] x) (𝓝 0) := by
    intro x hx
    by_cases hxz : x = z
    · rw [hxz]
      exact internalPhysicalMetric_tendsto_root hd ξ hD hz hfc hW
    · exact internalPhysicalMetric_tendsto_of_continuousAt hd ξ hD hx
        (hfc.continuousAt ((hD.sdiff isClosed_singleton).mem_nhds ⟨hx, hxz⟩))
  intro p hp
  obtain ⟨x, y⟩ := p
  have hx : x ∈ D := hp.1
  have hy : y ∈ D := hp.2
  set I := internalPhysicalMetric (weylPhysicalE d ξ f) D with hIdef
  have hfst : Tendsto (fun q : ℂ × ℂ => q.1) (𝓝[D ×ˢ D] (x, y)) (𝓝[D] x) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_fst.tendsto (x, y)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun q hq => hq.1⟩
  have hsnd : Tendsto (fun q : ℂ × ℂ => q.2) (𝓝[D ×ˢ D] (x, y)) (𝓝[D] y) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_snd.tendsto (x, y)).mono_left nhdsWithin_le_nhds,
      eventually_nhdsWithin_of_forall fun q hq => hq.2⟩
  have hu : Tendsto (fun q : ℂ × ℂ => I q.1 x + I q.2 y) (𝓝[D ×ˢ D] (x, y)) (𝓝 0) := by
    have h1 : Tendsto (fun q : ℂ × ℂ => I q.1 x) (𝓝[D ×ˢ D] (x, y)) (𝓝 0) :=
      (hlim x hx).comp hfst
    have h2 : Tendsto (fun q : ℂ × ℂ => I q.2 y) (𝓝[D ×ˢ D] (x, y)) (𝓝 0) :=
      (hlim y hy).comp hsnd
    simpa using h1.add h2
  have hl : Tendsto (fun q : ℂ × ℂ => I (x, y).1 (x, y).2 - (I q.1 x + I q.2 y)) (𝓝[D ×ˢ D] (x, y))
      (𝓝 (I (x, y).1 (x, y).2 - 0)) := tendsto_const_nhds.sub hu
  have hr : Tendsto (fun q : ℂ × ℂ => I (x, y).1 (x, y).2 + (I q.1 x + I q.2 y)) (𝓝[D ×ˢ D] (x, y))
      (𝓝 (I (x, y).1 (x, y).2 + 0)) := tendsto_const_nhds.add hu
  rw [sub_zero] at hl
  rw [add_zero] at hr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl hr ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hq1 : q.1 ∈ D := hq.1
    have hq2 : q.2 ∈ D := hq.2
    have t1 := htri x hx q.1 hq1 y hy
    have t2 := htri q.1 hq1 q.2 hq2 y hy
    have s1 := hsym x q.1
    have s2 := hsym q.2 y
    linarith
  · filter_upwards [self_mem_nhdsWithin] with q hq
    have hq1 : q.1 ∈ D := hq.1
    have hq2 : q.2 ∈ D := hq.2
    have t1 := htri q.1 hq1 x hx q.2 hq2
    have t2 := htri x hx y hy q.2 hq2
    have s1 := hsym y q.2
    linarith

/-- **Length-metric fields of the rooted internal physical metric** (for n4's `IsLengthMetricOn (ball c₂ r₂)`). On an open
connected `D ∋ z`, with `d` an `IsEuclideanLengthMetric` and `f` continuous on `D ∖ {z}` with the insertion limit `hW`:
`I x x = 0`, `I` symmetric, the triangle inequality on `D`, `ofReal (I x y) = internalMetric I D x y` on `D`, and joint
continuity on `D × D`. Not included: `eq_of_eq_zero` and `isOpen_iff` (ChatGPT chat 192). -/
theorem internalPhysicalMetric_lengthFields {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ)
    {f : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {z : ℂ} (hz : z ∈ D)
    (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    (∀ x ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x x = 0) ∧
    (∀ x y, internalPhysicalMetric (weylPhysicalE d ξ f) D x y = internalPhysicalMetric (weylPhysicalE d ξ f) D y x) ∧
    (∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x w ≤
        internalPhysicalMetric (weylPhysicalE d ξ f) D x y + internalPhysicalMetric (weylPhysicalE d ξ f) D y w) ∧
    (∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (internalPhysicalMetric (weylPhysicalE d ξ f) D x y) =
        internalMetric (internalPhysicalMetric (weylPhysicalE d ξ f) D) D x y) ∧
    ContinuousOn (fun q : ℂ × ℂ => internalPhysicalMetric (weylPhysicalE d ξ f) D q.1 q.2) (D ×ˢ D) := by
  obtain ⟨hsym, htri, hlen⟩ := weylPhysicalE_internalPhysical_props_root hd ξ hD hDc hz hfc hW
  exact ⟨fun x hx => internalPhysicalMetric_self_eq_zero hd ξ f D hx, hsym, htri, hlen,
    internalPhysicalMetric_continuousOn_root hd ξ hD hDc hz hfc hW⟩

/-- `I` is symmetric (`weylPhysicalE` is symmetric, `internalMetric_symm_of_symm`). -/
theorem internalPhysicalMetric_symm_root {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) (f : ℂ → ℝ)
    (D : Set ℂ) : ∀ a b, internalPhysicalMetric (weylPhysicalE d ξ f) D a b =
      internalPhysicalMetric (weylPhysicalE d ξ f) D b a :=
  internalPhysicalMetric_symm_of (internalMetric_symm_of_symm (weylPhysicalE_symm hd ξ f) D)

/-- One-variable continuity `I(·, x) → 0` within `D` at every `x ∈ D` (the root case is he_cont). -/
theorem internalPhysicalMetric_tendsto_pt {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) {x : ℂ} (hx : x ∈ D) :
    Tendsto (fun y => internalPhysicalMetric (weylPhysicalE d ξ f) D y x) (𝓝[D] x) (𝓝 0) := by
  by_cases hxz : x = z
  · rw [hxz]
    exact internalPhysicalMetric_tendsto_root hd ξ hD hz hfc hW
  · exact internalPhysicalMetric_tendsto_of_continuousAt hd ξ hD hx
      (hfc.continuousAt ((hD.sdiff isClosed_singleton).mem_nhds ⟨hx, hxz⟩))

/-- **Good radius.** For `x ∈ D` there is `r > 0` with `ball x r ⊆ D` and `z ∉ ball x r ∖ {x}`. -/
theorem exists_good_radius {D : Set ℂ} (hD : IsOpen D) {z x : ℂ} (hx : x ∈ D) :
    ∃ r > 0, ball x r ⊆ D ∧ ∀ w ∈ ball x r, w ≠ x → w ≠ z := by
  obtain ⟨r1, hr1, hball⟩ := Metric.isOpen_iff.1 hD x hx
  by_cases hxz : x = z
  · exact ⟨r1, hr1, hball, fun w _ hwx hwz => hwx (hwz.trans hxz.symm)⟩
  · have hpos : 0 < dist z x := dist_pos.2 (Ne.symm hxz)
    refine ⟨min r1 (dist z x), lt_min hr1 hpos, (ball_subset_ball (min_le_left _ _)).trans hball,
      fun w hw _ hwz => ?_⟩
    have h := mem_ball.1 hw
    rw [hwz] at h
    exact lt_irrefl _ (lt_of_lt_of_le h (min_le_right _ _))

/-- **Exit lemma (crossing cost).** If `f` is continuous on the punctured ball `ball q r ∖ {q}`, then every path from `q`
leaving `ball q r` has Weyl cost at least a fixed `η > 0` (`exists_exit_data` with base point `q`). -/
theorem weylScaling_ge_of_exit {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ} {q : ℂ} {r : ℝ}
    (hr : 0 < r) (hfc : ContinuousOn f (ball q r \ {q})) :
    ∃ η > 0, ∀ b, b ∉ ball q r → ENNReal.ofReal η ≤ weylScaling d ξ f q b := by
  obtain ⟨c0, c2, m, hc0, hc02, hm, hexit⟩ :=
    exists_exit_data hd ξ isOpen_ball (mem_ball_self hr) hfc
  refine ⟨m * (c2 - c0), mul_pos hm (by linarith), fun b hb => ?_⟩
  by_contra hlt
  have hlt' := not_le.1 hlt
  unfold weylScaling at hlt'
  simp only [iInf_lt_iff] at hlt'
  obtain ⟨T, p, hp, hp0, hpT, hcost⟩ := hlt'
  have h0 : d q (p 0) < c0 := by rw [hp0, hd.self_eq_zero]; exact hc0
  have hT : p T ∈ ball q r := hexit T p hp h0 hcost T ⟨hp.1, le_rfl⟩
  rw [hpT] at hT
  exact hb hT

/-- **Internal lower bound across the annulus.** If every point outside `ball q r` is at Weyl distance at least `η`
from `q`, and `b ∈ D ∖ ball q r`, then the internal physical distance from `q` to `b` in `D` is at least `η`: every path in
`D` from `q` to `b` has, at its last point before its first exit from `ball q r`, a partition step of Weyl cost `≥ η`. -/
theorem internalPhysicalMetric_ge_of_exit {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} {q b : ℂ} {r η : ℝ} (hq : q ∈ D) (_hb : b ∈ D) (hbr : b ∉ ball q r)
    (hsep : ∀ w, w ∉ ball q r → ENNReal.ofReal η ≤ weylScaling d ξ f q w)
    (hfin : ∀ x ∈ D, ∀ y ∈ D, weylScaling d ξ f x y ≠ ⊤)
    (hIfin : internalMetric (weylPhysicalE d ξ f) D q b ≠ ⊤) :
    η ≤ internalPhysicalMetric (weylPhysicalE d ξ f) D q b := by
  have hE : ENNReal.ofReal η ≤ internalMetric (weylPhysicalE d ξ f) D q b := by
    refine le_iInf₂ fun P hPD => ?_
    set S : Set ℝ := {u | u ∈ Icc (0:ℝ) 1 ∧ P.extend u ∉ ball q r} with hSdef
    have hSne : S.Nonempty := ⟨1, ⟨⟨zero_le_one, le_rfl⟩, by rw [Path.extend_one]; exact hbr⟩⟩
    have hSc : IsClosed S := by
      have heq : S = Icc 0 1 ∩ (P.extend ⁻¹' ball q r)ᶜ := by
        ext u
        simp [hSdef]
      rw [heq]
      exact isClosed_Icc.inter (P.continuous_extend.isOpen_preimage _ isOpen_ball).isClosed_compl
    obtain ⟨⟨hτ0, hτ1⟩, hτout⟩ : sInf S ∈ S := hSc.csInf_mem hSne ⟨0, fun u hu => hu.1.1⟩
    obtain ⟨u, hu0, hu1, hmono, hrange⟩ : ∃ u : ℕ → ℝ, u 0 = 0 ∧ u 1 = sInf S ∧ Monotone u ∧
        ∀ i, u i ∈ Icc (0:ℝ) 1 := by
      refine ⟨fun i => if i = 0 then 0 else if i = 1 then sInf S else 1, by simp, by simp, ?_, ?_⟩
      · refine monotone_nat_of_le_succ fun n => ?_
        rcases n with _ | _ | n <;> simp [hτ0, hτ1]
      · intro i
        dsimp only
        split_ifs
        · exact ⟨le_rfl, zero_le_one⟩
        · exact ⟨hτ0, hτ1⟩
        · exact ⟨zero_le_one, le_rfl⟩
    have hsum : ENNReal.ofReal (weylPhysicalE d ξ f (P.extend (u 1)) (P.extend (u 0))) ≤
        curveLength (weylPhysicalE d ξ f) P.extend 0 1 := by
      refine le_iSup_of_le ((2 : ℕ), (⟨u, hmono, hrange⟩ : {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0:ℝ) 1})) ?_
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      exact le_self_add
    have hPτ : P.extend (sInf S) ∈ D := by
      have h : P.extend (sInf S) = P ⟨sInf S, hτ0, hτ1⟩ := Path.extend_extends' P ⟨sInf S, hτ0, hτ1⟩
      rw [h]
      exact hPD _
    have hηle : η ≤ weylPhysicalE d ξ f q (P.extend (sInf S)) :=
      (ENNReal.ofReal_le_iff_le_toReal (hfin q hq _ hPτ)).1 (hsep _ hτout)
    have hu1' := hsum
    rw [hu1, hu0] at hu1'
    calc ENNReal.ofReal η ≤ ENNReal.ofReal (weylPhysicalE d ξ f (P.extend (sInf S)) q) := by
          rw [weylPhysicalE_symm hd ξ f (P.extend (sInf S)) q]
          exact ENNReal.ofReal_le_ofReal hηle
      _ = ENNReal.ofReal (weylPhysicalE d ξ f (P.extend (sInf S)) (P.extend 0)) := by
          rw [Path.extend_zero]
      _ ≤ curveLength (weylPhysicalE d ξ f) P.extend 0 1 := hu1'
  exact (ENNReal.ofReal_le_iff_le_toReal hIfin).1 hE

/-- **Non-degeneracy** (field `eq_of_eq_zero` of `IsLengthMetricOn`): the internal physical distance between distinct
points of `D` is positive. -/
theorem internalPhysicalMetric_eq_of_eq_zero {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {z : ℂ} (hz : z ∈ D) (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    ∀ x ∈ D, ∀ y ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x y = 0 → x = y := by
  intro x hx y hy h0
  by_contra hne
  obtain ⟨r0, hr0, hD0, hz0⟩ := exists_good_radius hD (z := z) hx
  have hwpos : 0 < dist y x := dist_pos.2 (Ne.symm hne)
  have hr : 0 < min r0 (dist y x) := lt_min hr0 hwpos
  have hrD : ball x (min r0 (dist y x)) ⊆ D := (ball_subset_ball (min_le_left _ _)).trans hD0
  have hfc' : ContinuousOn f (ball x (min r0 (dist y x)) \ {x}) :=
    hfc.mono fun w hw => ⟨hrD hw.1, hz0 w (ball_subset_ball (min_le_left _ _) hw.1) hw.2⟩
  obtain ⟨η, hη, hsep⟩ := weylScaling_ge_of_exit hd ξ hr hfc'
  have hyr : y ∉ ball x (min r0 (dist y x)) := fun h =>
    absurd (mem_ball.1 h) (not_lt.2 (min_le_right _ _))
  have hfin := finite_on_disk_root hd ξ hD hDc hz hfc hW
  have hle := internalPhysicalMetric_ge_of_exit hd ξ hx hy hyr hsep hfin.1 (hfin.2 x hx y hy)
  linarith

/-- **Euclidean topology** (field `isOpen_iff` of `IsLengthMetricOn`): a subset `U ⊆ D` is open iff every point of `U` has
an internal-distance neighbourhood in `D` inside `U`. -/
theorem internalPhysicalMetric_isOpen_iff {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {z : ℂ} (hz : z ∈ D) (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    ∀ U ⊆ D, (IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ w ∈ D,
      internalPhysicalMetric (weylPhysicalE d ξ f) D x w < ε → w ∈ U) := by
  intro U hUD
  have hfin := finite_on_disk_root hd ξ hD hDc hz hfc hW
  constructor
  · intro hU x hx
    obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.1 hU x hx
    obtain ⟨r1, hr1, hD1, hz1⟩ := exists_good_radius hD (z := z) (hUD hx)
    have hr : 0 < min r0 r1 := lt_min hr0 hr1
    have hrD : ball x (min r0 r1) ⊆ D := (ball_subset_ball (min_le_right _ _)).trans hD1
    have hfc' : ContinuousOn f (ball x (min r0 r1) \ {x}) :=
      hfc.mono fun w hw => ⟨hrD hw.1, hz1 w (ball_subset_ball (min_le_right _ _) hw.1) hw.2⟩
    obtain ⟨η, hη, hsep⟩ := weylScaling_ge_of_exit hd ξ hr hfc'
    refine ⟨η, hη, fun w hwD hw => ?_⟩
    by_contra hwU
    have hwr : w ∉ ball x (min r0 r1) := fun h => hwU (hball (ball_subset_ball (min_le_left _ _) h))
    have hle := internalPhysicalMetric_ge_of_exit hd ξ (hUD hx) hwD hwr hsep hfin.1 (hfin.2 x (hUD hx) w hwD)
    linarith
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hxU
    obtain ⟨ε, hε, hεU⟩ := h x hxU
    have hxD : x ∈ D := hUD hxU
    have hlim := internalPhysicalMetric_tendsto_pt hd ξ hD hz hfc hW hxD
    have hev : ∀ᶠ w in 𝓝[D] x, internalPhysicalMetric (weylPhysicalE d ξ f) D w x < ε :=
      hlim.eventually (gt_mem_nhds hε)
    rw [eventually_nhdsWithin_iff] at hev
    filter_upwards [hev, hD.mem_nhds hxD] with w hw hwD
    apply hεU w hwD
    rw [internalPhysicalMetric_symm_root hd ξ f D x w]
    exact hw hwD

/-- **Full length-metric fields of the rooted internal physical metric**: all fields of `IsLengthMetricOn D I` except the
ones for the decoder identity (which n4 derives from (20)): self-distance, symmetry, triangle inequality, length identity,
joint continuity on `D × D`, non-degeneracy, and the Euclidean topology. -/
theorem internalPhysicalMetric_lengthFields_full {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ)
    {f : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {z : ℂ} (hz : z ∈ D)
    (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    (∀ x ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x x = 0) ∧
    (∀ x y, internalPhysicalMetric (weylPhysicalE d ξ f) D x y = internalPhysicalMetric (weylPhysicalE d ξ f) D y x) ∧
    (∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x w ≤
        internalPhysicalMetric (weylPhysicalE d ξ f) D x y + internalPhysicalMetric (weylPhysicalE d ξ f) D y w) ∧
    (∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (internalPhysicalMetric (weylPhysicalE d ξ f) D x y) =
        internalMetric (internalPhysicalMetric (weylPhysicalE d ξ f) D) D x y) ∧
    ContinuousOn (fun q : ℂ × ℂ => internalPhysicalMetric (weylPhysicalE d ξ f) D q.1 q.2) (D ×ˢ D) ∧
    (∀ x ∈ D, ∀ y ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x y = 0 → x = y) ∧
    (∀ U ⊆ D, (IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ w ∈ D,
      internalPhysicalMetric (weylPhysicalE d ξ f) D x w < ε → w ∈ U)) :=
  ⟨(internalPhysicalMetric_lengthFields hd ξ hD hDc hz hfc hW).1,
    (internalPhysicalMetric_lengthFields hd ξ hD hDc hz hfc hW).2.1,
    (internalPhysicalMetric_lengthFields hd ξ hD hDc hz hfc hW).2.2.1,
    (internalPhysicalMetric_lengthFields hd ξ hD hDc hz hfc hW).2.2.2.1,
    (internalPhysicalMetric_lengthFields hd ξ hD hDc hz hfc hW).2.2.2.2,
    internalPhysicalMetric_eq_of_eq_zero hd ξ hD hDc hz hfc hW,
    internalPhysicalMetric_isOpen_iff hd ξ hD hDc hz hfc hW⟩

end HarmonicBalls
