import HarmonicBalls.FirstPass.S11r.RootedRootContinuity

/-!
# First pass, finiteness of the rooted physical metric (fp-S11r, owner n2; R2 Steps B-C)

Replaces the hypothesis `hfM : ∀ w ∈ D, exp (ξ f w) ≤ M` of `RootedFinite.lean` and `RootedHe.lean` by the two hypotheses
that hold for the rooted weight: `ContinuousOn f (D \ {z})` and the ambient limit `weylScaling d ξ f x z → 0` as `x → z`
(the frozen input `RootedPhysicalMetricContinuousAtInsertionFrozen`, instantiated). The old hypothesis is false there: for
`z ∈ D` and `ξ γ > 0` the weight `exp (ξ f)` is unbounded near `z`, since `f ∼ -γ log|w - z|`.

Route (R2 answer, Steps B-C; notes/fp-gaps/CHATGPT-n2-R2-rooted-length.md section 3):
(B) On `O = D ∖ {z}`, open and connected (`isPreconnected_diff_singleton_of_root`), two points are joined by a path of finite
`d`-length whose compact range carries a bound on the weight: their Weyl distance and internal physical metric are finite
(`finite_on_punctured`).
(C) Some `q ∈ O` has `W(q,z) < ∞` and `I_D(q,z) < ∞` (near the root, `internalMetric_le_weylScaling_eventually`). Every
`x ∈ D` is then joined to `q` with finite cost, and the triangle inequalities give finiteness on `D × D`
(`finite_on_disk_root`).

Terminology: Weyl scaling `e^{ξ f} · d` (Duplantier-Sheffield; Gwynne-Miller); internal metric `D(·,·;U)` (Armstrong-Kuusi-Mourrat).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- The punctured disc `B(z, r) ∖ {z}` is preconnected: it is the image of the half-plane `{Re w < log r}` under
`w ↦ z + exp w`, since `exp` maps that half-plane onto the punctured disc of radius `r` about `0`. -/
theorem isPreconnected_ball_diff_center {z : ℂ} {r : ℝ} (hr : 0 < r) :
    IsPreconnected (ball z r \ {z}) := by
  have hconv : Convex ℝ {w : ℂ | w.re < Real.log r} :=
    convex_halfSpace_lt (f := Complex.re) ⟨fun x y => by simp, fun c x => by simp⟩ _
  have himg : IsPreconnected ((fun w : ℂ => z + Complex.exp w) '' {w : ℂ | w.re < Real.log r}) :=
    hconv.isPreconnected.image _ (by fun_prop)
  have heq : (fun w : ℂ => z + Complex.exp w) '' {w : ℂ | w.re < Real.log r} = ball z r \ {z} := by
    ext u
    constructor
    · rintro ⟨w, hw, rfl⟩
      show z + Complex.exp w ∈ ball z r \ {z}
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_exp]
        calc Real.exp w.re < Real.exp (Real.log r) := Real.exp_lt_exp.2 hw
          _ = r := Real.exp_log hr
      · intro h
        have h0 : Complex.exp w = 0 := by linear_combination (mem_singleton_iff.1 h)
        exact Complex.exp_ne_zero w h0
    · rintro ⟨hu, huz⟩
      have hne : u - z ≠ 0 := fun h => huz (mem_singleton_iff.2 (sub_eq_zero.1 h))
      refine ⟨Complex.log (u - z), ?_, ?_⟩
      · show (Complex.log (u - z)).re < Real.log r
        rw [Complex.log_re]
        have hpos : 0 < ‖u - z‖ := norm_pos_iff.2 hne
        exact Real.log_lt_log hpos (by rw [← dist_eq_norm]; exact mem_ball.1 hu)
      · show z + Complex.exp (Complex.log (u - z)) = u
        rw [Complex.exp_log hne]
        ring
  rw [← heq]
  exact himg

/-- Separation step: if `D` is preconnected and the punctured disc `B(z,r) ∖ {z}` lies in the open set `v`, while the
open set `u` meets `D ∖ {z}` and is disjoint from `v` there, then `u` misses `z` and `u`, `v ∪ B(z,r)` disconnect `D`. -/
theorem sep_aux_root {D : Set ℂ} (hDp : IsPreconnected D) {z : ℂ} {r : ℝ} (hr : 0 < r) (hBD : ball z r ⊆ D)
    {u v : Set ℂ} (hu : IsOpen u) (hv : IsOpen v)
    (hdisj : ∀ w ∈ D \ {z}, w ∈ u → w ∈ v → False) (hcov : D \ {z} ⊆ u ∪ v)
    (hBv : ball z r \ {z} ⊆ v) {a b : ℂ} (ha : a ∈ D \ {z}) (hau : a ∈ u)
    (hb : b ∈ D \ {z}) (hbv : b ∈ v) : False := by
  have hzu : z ∉ u := by
    intro hzu
    have hev : ∀ᶠ w in 𝓝[≠] z, w ∈ u ∩ ball z r :=
      nhdsWithin_le_nhds (inter_mem (hu.mem_nhds hzu) (isOpen_ball.mem_nhds (mem_ball_self hr)))
    obtain ⟨w, ⟨hwu, hwr⟩, hwz⟩ := (hev.and self_mem_nhdsWithin).exists
    exact hdisj w ⟨hBD hwr, hwz⟩ hwu (hBv ⟨hwr, hwz⟩)
  have hsub : D ⊆ u ∪ (v ∪ ball z r) := by
    intro w hw
    by_cases hwz : w = z
    · exact Or.inr (Or.inr (hwz ▸ mem_ball_self hr))
    · rcases hcov ⟨hw, hwz⟩ with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  obtain ⟨w, hwD, hwu, hwV⟩ := hDp u (v ∪ ball z r) hu (hv.union isOpen_ball) hsub
    ⟨a, ha.1, hau⟩ ⟨b, hb.1, Or.inl hbv⟩
  have hwz : w ≠ z := fun h => hzu (h ▸ hwu)
  by_cases hwB : w ∈ ball z r
  · exact hdisj w ⟨hwD, hwz⟩ hwu (hBv ⟨hwB, hwz⟩)
  · exact hdisj w ⟨hwD, hwz⟩ hwu (hwV.resolve_right hwB)

/-- The complement of a point in an open preconnected set of `ℂ` is preconnected (R2 Step B; Mathlib has only the
whole-space version `isConnected_compl_singleton_of_one_lt_rank`). -/
theorem isPreconnected_diff_singleton_of_root {D : Set ℂ} (hD : IsOpen D) (hDp : IsPreconnected D) {z : ℂ}
    (hz : z ∈ D) : IsPreconnected (D \ {z}) := by
  obtain ⟨r, hr, hBD⟩ := Metric.isOpen_iff.1 hD z hz
  have hBp := isPreconnected_ball_diff_center (z := z) hr
  have hB : ball z r \ {z} ⊆ D \ {z} := sdiff_subset_sdiff_left hBD
  intro u v hu hv hcov ha hb
  obtain ⟨a, ha⟩ := ha
  obtain ⟨b, hb⟩ := hb
  by_contra hne
  have hdisj : ∀ w ∈ D \ {z}, w ∈ u → w ∈ v → False :=
    fun w hw hwu hwv => hne ⟨w, hw, hwu, hwv⟩
  have hcovB : ball z r \ {z} ⊆ u ∪ v := fun w hw => hcov (hB hw)
  by_cases h1 : (ball z r \ {z} ∩ u).Nonempty
  · by_cases h2 : (ball z r \ {z} ∩ v).Nonempty
    · obtain ⟨w, hw, hwuv⟩ := hBp u v hu hv hcovB h1 h2
      exact hdisj w (hB hw) hwuv.1 hwuv.2
    · have hBu : ball z r \ {z} ⊆ u := fun w hw => by
        rcases hcovB hw with h | h
        · exact h
        · exact absurd ⟨w, hw, h⟩ h2
      exact sep_aux_root hDp hr hBD hv hu (fun w hw hwv hwu => hdisj w hw hwu hwv)
        (fun w hw => (hcov hw).symm) hBu hb.1 hb.2 ha.1 ha.2
  · have hBv : ball z r \ {z} ⊆ v := fun w hw => by
      rcases hcovB hw with h | h
      · exact absurd ⟨w, hw, h⟩ h1
      · exact h
    exact sep_aux_root hDp hr hBD hu hv hdisj hcov hBv ha.1 ha.2 hb.1 hb.2

/-- A path of finite `d`-length in `O`, along which `f` is continuous, gives finite Weyl distance between its endpoints and
finite `e`-length (`weylScaling_le_mul_curveLength_of_subset`, `pathLength_weylScaling_toReal_le`, with the weight bounded on
the compact range of the path by `exists_expWeight_bound`). -/
theorem weylScaling_pathLength_ne_top_of_range {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {O : Set ℂ} (hfc : ContinuousOn f O) {x y : ℂ} (P : Path x y) (hPO : ∀ t, P t ∈ O)
    (hfin : pathLength d P < ⊤) :
    weylScaling d ξ f x y ≠ ⊤ ∧ pathLength (weylPhysicalE d ξ f) P ≠ ⊤ := by
  have hK : IsCompact (range P) := isCompact_range P.continuous
  obtain ⟨M, hM, hfM⟩ := exists_expWeight_bound hK (hfc.mono (range_subset_iff.2 hPO)) ξ
  have hPM : ∀ t, P t ∈ range P := fun t => mem_range_self t
  have hfin0 : curveLength d P.extend 0 1 < ⊤ := hfin
  have hPD' : ∀ t ∈ Icc (0 : ℝ) 1, P.extend t ∈ range P := fun t ht =>
    ⟨⟨t, ht⟩, (Path.extend_extends' P ⟨t, ht⟩).symm⟩
  have hW := weylScaling_le_mul_curveLength_of_subset hd ξ hM hfM zero_le_one
    P.continuous_extend.continuousOn hPD' hfin0
  rw [Path.extend_zero, Path.extend_one] at hW
  have hE := pathLength_weylScaling_toReal_le hd ξ hM hfM P hPM hfin
  have hmul : ENNReal.ofReal M * pathLength d P ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne
  exact ⟨ne_top_of_le_ne_top hmul hW, ne_top_of_le_ne_top hmul hE⟩

/-- **Finiteness on `O = D ∖ {z}`** (R2 Step B). For `x, y ∈ D ∖ {z}` the Weyl distance and the internal physical metric of
`weylPhysicalE d ξ f` on `D` are finite. -/
theorem finite_on_punctured {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ} {D : Set ℂ}
    (hD : IsOpen D) {z : ℂ} (hz : z ∈ D) (hDp : IsPreconnected D) (hfc : ContinuousOn f (D \ {z}))
    {x y : ℂ} (hx : x ∈ D \ {z}) (hy : y ∈ D \ {z}) :
    weylScaling d ξ f x y ≠ ⊤ ∧ internalMetric (weylPhysicalE d ξ f) D x y ≠ ⊤ := by
  have hO : IsOpen (D \ {z}) := hD.sdiff isClosed_singleton
  have hOc : IsConnected (D \ {z}) := ⟨⟨x, hx⟩, isPreconnected_diff_singleton_of_root hD hDp hz⟩
  have hlt : internalMetric d (D \ {z}) x y < ⊤ :=
    lt_top_iff_ne_top.2 (S11m.internalMetric_ne_top_of_isConnected hd hO hOc hx hy)
  unfold internalMetric at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hPO, hPlt⟩ := iInf_lt_iff.1 hP
  obtain ⟨hW, hE⟩ := weylScaling_pathLength_ne_top_of_range hd ξ hfc P hPO hPlt
  refine ⟨hW, ne_top_of_le_ne_top hE ?_⟩
  unfold internalMetric
  exact iInf₂_le P (fun t => (hPO t).1)

/-- The triangle inequality of the physical metric on `D`, from the finiteness of the Weyl distance on `D × D`
(`RootedLocal.toReal_triangle_on`). -/
theorem weylPhysicalE_tri_of_finite {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {D : Set ℂ} (hWD : ∀ x ∈ D, ∀ y ∈ D, weylScaling d ξ f x y ≠ ⊤) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D,
      weylPhysicalE d ξ f x w ≤ weylPhysicalE d ξ f x y + weylPhysicalE d ξ f y w := by
  intro x hx y hy w hw
  unfold weylPhysicalE
  exact RootedLocal.toReal_triangle_on hd (hWD x hx y hy) (hWD y hy w hw)

/-- **Finiteness on `D × D`** (R2 Step C). With `ContinuousOn f (D ∖ {z})` and the ambient limit at `z`, the Weyl distance and
the internal physical metric of `weylPhysicalE d ξ f` on `D` are finite on `D × D`. -/
theorem finite_on_disk_root {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ} {D : Set ℂ}
    (hD : IsOpen D) (hDc : IsConnected D) {z : ℂ} (hz : z ∈ D) (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    (∀ x ∈ D, ∀ y ∈ D, weylScaling d ξ f x y ≠ ⊤) ∧
      (∀ x ∈ D, ∀ y ∈ D, internalMetric (weylPhysicalE d ξ f) D x y ≠ ⊤) := by
  have hkey := internalMetric_le_weylScaling_eventually hd ξ hD hz hfc hW
  have hev0 : ∀ᶠ x in 𝓝 z, x ∈ D ∧ weylScaling d ξ f x z ≠ ⊤ ∧
      internalMetric (weylPhysicalE d ξ f) D x z ≠ ⊤ := by
    filter_upwards [hD.mem_nhds hz, hkey, hW.eventually (gt_mem_nhds ENNReal.zero_lt_top)] with x hxD hxk hxW
    exact ⟨hxD, ne_top_of_lt hxW, ne_top_of_le_ne_top (ne_top_of_lt hxW) hxk⟩
  have hev1 : ∀ᶠ x in 𝓝[≠] z, x ∈ D ∧ weylScaling d ξ f x z ≠ ⊤ ∧
      internalMetric (weylPhysicalE d ξ f) D x z ≠ ⊤ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds hev0
  obtain ⟨q, ⟨hqD, hqW, hqI⟩, hqz⟩ := (hev1.and self_mem_nhdsWithin).exists
  have hqO : q ∈ D \ {z} := ⟨hqD, hqz⟩
  have hsymI : ∀ x y, internalMetric (weylPhysicalE d ξ f) D x y =
      internalMetric (weylPhysicalE d ξ f) D y x :=
    internalMetric_symm_of_symm (weylPhysicalE_symm hd ξ f) D
  have hfinq : ∀ x ∈ D, weylScaling d ξ f x q ≠ ⊤ ∧
      internalMetric (weylPhysicalE d ξ f) D x q ≠ ⊤ := by
    intro x hx
    by_cases hxz : x = z
    · rw [hxz, IsEuclideanLengthMetric.weylScaling_symm hd ξ f z q, hsymI z q]
      exact ⟨hqW, hqI⟩
    · exact finite_on_punctured hd ξ hD hz hDc.isPreconnected hfc ⟨hx, hxz⟩ hqO
  have hWD : ∀ x ∈ D, ∀ y ∈ D, weylScaling d ξ f x y ≠ ⊤ := by
    intro x hx y hy
    have h := hd.weylScaling_triangle ξ f x q y
    have hqy : weylScaling d ξ f q y ≠ ⊤ := by
      rw [IsEuclideanLengthMetric.weylScaling_symm hd ξ f q y]
      exact (hfinq y hy).1
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨(hfinq x hx).1, hqy⟩) h
  refine ⟨hWD, fun x hx y hy => ?_⟩
  have hEtri := weylPhysicalE_tri_of_finite hd ξ hWD
  have h := internalMetric_triangle_on (weylPhysicalE d ξ f) (D := D) (weylPhysicalE_symm hd ξ f)
    (fun x _ => weylPhysicalE_self hd ξ f x) hEtri (x := x) (y := q) (z := y)
  have hqy : internalMetric (weylPhysicalE d ξ f) D q y ≠ ⊤ := by
    rw [hsymI q y]
    exact (hfinq y hy).2
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨(hfinq x hx).2, hqy⟩) h

/-- **Internal-side hypotheses `he_symm`, `he_tri`, `he_len` for the Weyl-scaled physical metric, with the rooted
hypotheses** (replaces `weylPhysicalE_internalPhysical_props` of `RootedHe.lean`, whose hypothesis `hfM` is false for the
rooted weight). -/
theorem weylPhysicalE_internalPhysical_props_root {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ)
    {f : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {z : ℂ} (hz : z ∈ D)
    (hfc : ContinuousOn f (D \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0)) :
    (∀ x y, internalPhysicalMetric (weylPhysicalE d ξ f) D x y =
        internalPhysicalMetric (weylPhysicalE d ξ f) D y x) ∧
    (∀ x ∈ D, ∀ y ∈ D, ∀ w ∈ D, internalPhysicalMetric (weylPhysicalE d ξ f) D x w ≤
        internalPhysicalMetric (weylPhysicalE d ξ f) D x y + internalPhysicalMetric (weylPhysicalE d ξ f) D y w) ∧
    (∀ x ∈ D, ∀ y ∈ D, ENNReal.ofReal (internalPhysicalMetric (weylPhysicalE d ξ f) D x y) =
        internalMetric (internalPhysicalMetric (weylPhysicalE d ξ f) D) D x y) := by
  have hs := weylPhysicalE_symm hd ξ f
  obtain ⟨hWD, hfin⟩ := finite_on_disk_root hd ξ hD hDc hz hfc hW
  refine ⟨internalPhysicalMetric_symm_of (internalMetric_symm_of_symm hs D), ?_,
    internalPhysicalMetric_length_eq hs hfin⟩
  exact internalPhysicalMetric_tri_of
    (fun x hx y hy w hw => internalMetric_triangle_on _ hs (fun x _ => weylPhysicalE_self hd ξ f x)
      (weylPhysicalE_tri_of_finite hd ξ hWD)) hfin

end HarmonicBalls
