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

end HarmonicBalls
