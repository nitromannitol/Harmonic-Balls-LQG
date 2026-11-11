import HarmonicBalls.FirstPass.S11m.WeylLengthCompact
import HarmonicBalls.Steps.Sec11.WeylLocalEdges

/-! # Local Weyl comparison near a point (R1, part 1)

Let `d` be a Euclidean length metric (`IsEuclideanLengthMetric d`) and let two weights `f`, `g` agree on a Euclidean
neighbourhood of a point `q`. Then the Weyl-scaled distances `weylScaling d ξ f` and `weylScaling d ξ g` agree on all
pairs of points in a small `d`-ball around `q`, and are finite there.

The proof is the exit argument (Step 3), made per curve: a length-parametrized
curve from a point of the small ball which leaves the larger `d`-ball `{d q · < s}` has weighted cost at least
`e^{Lb} (s - t)`, where `Lb` is a lower bound of `ξ · f` on that ball. Only the weights on the `d`-ball are used; the
weight `g` may be singular (for instance `g = -α log |· - z|` with `z` outside the ball), and no global finiteness or
length property of the scaled metric of `g` is needed.

Naming follows Gwynne-Miller (arXiv:1905.00383v3, §1.2, eq. (1.8): `e^{ξ f} · D`) and Armitage-Gardiner for the
potential-theoretic notions; the relevant HB objects are `weylScaling`, `IsLengthParametrized`, `curveLength`. -/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace RootedLocal

variable {d : ℂ → ℂ → ℝ}

/-- The `d`-ball `{w | d q w < r}` is open in the Euclidean topology (`d` is a Euclidean length metric). -/
theorem isOpen_dBall (hd : IsEuclideanLengthMetric d) (q : ℂ) (r : ℝ) :
    IsOpen {w : ℂ | d q w < r} := by
  rw [hd.isOpen_iff]
  intro z hz
  simp only [mem_ofPred_eq] at hz
  refine ⟨r - d q z, by linarith, fun w hw => ?_⟩
  simp only [mem_ofPred_eq] at hw ⊢
  have h := hd.triangle q z w
  linarith

/-- Nonnegativity of a length metric, from symmetry and the triangle inequality. -/
theorem nonneg_of_length (hd : IsEuclideanLengthMetric d) (a b : ℂ) : 0 ≤ d a b := by
  have h := hd.triangle a b a
  rw [hd.self_eq_zero, hd.symm b a] at h
  linarith

/-- For a point `p a` of a `d`-curve, the `d`-distance to `p b` (with `a ≤ b`) is at most the `d`-length of the piece
`[a, b]` (one-piece partition). -/
theorem ofReal_dist_le_curveLength_pair (hd : IsEuclideanLengthMetric d) (p : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ENNReal.ofReal (d (p a) (p b)) ≤ curveLength d p a b := by
  unfold curveLength
  have hmono : Monotone (fun n : ℕ => if n = 0 then a else b) := by
    intro n m hnm
    by_cases hn : n = 0
    · subst hn
      by_cases hm : m = 0
      · subst hm
        exact le_rfl
      · simp only [hm, ite_false, ite_true]
        exact hab
    · have hm : m ≠ 0 := by omega
      simp only [hn, hm, ite_false]
      exact le_rfl
  refine le_iSup_of_le (1, ⟨fun n => if n = 0 then a else b, hmono, fun i => ?_⟩) ?_
  · by_cases hi : i = 0
    · simp only [hi, ite_true]
      exact ⟨le_rfl, hab⟩
    · simp only [hi, ite_false]
      exact ⟨hab, le_rfl⟩
  · simp only [Finset.range_one, Finset.sum_singleton, zero_add, ite_true, Nat.one_ne_zero, ite_false]
    rw [hd.symm (p b) (p a)]

/-- The `d`-distance from the starting point of a length-parametrized curve to `p t` is at most `t`. -/
theorem dist_start_le_of_lengthParam (hd : IsEuclideanLengthMetric d) {p : ℝ → ℂ} {T t : ℝ}
    (hp : IsLengthParametrized d p T) (ht : t ∈ Icc 0 T) : d (p 0) (p t) ≤ t := by
  have h1 := ofReal_dist_le_curveLength_pair hd p ht.1
  rw [hp.2.2 0 t le_rfl ht.1 ht.2, sub_zero] at h1
  exact (ENNReal.ofReal_le_ofReal_iff ht.1).mp h1

/-- **Per-curve first-exit bound.** A length-parametrized curve `p : [0, T] → ℂ` starting at `x` with
`d q x < t` which reaches the sphere `{d q · ≥ s}` has weighted cost at least `e^{Lb} (s - t)`, provided
`ξ · k ≥ Lb` on `{d q · < s}`. The first exit time `τ₁ = inf {τ ∈ [0, T] | s ≤ d q (p τ)}` is attained, the curve
stays in `{d q · < s}` before `τ₁`, and `τ₁ ≥ s - t` by the triangle inequality. -/
theorem cost_ge_of_exit (hd : IsEuclideanLengthMetric d) {ξ Lb s t : ℝ} {q : ℂ} {k : ℂ → ℝ}
    (hlow : ∀ w, d q w < s → Lb ≤ ξ * k w)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized d p T) {x : ℂ} (hx0 : p 0 = x)
    (hxt : d q x < t) (hexit : ∃ τ ∈ Icc 0 T, s ≤ d q (p τ)) :
    ENNReal.ofReal (Real.exp Lb * (s - t)) ≤
      ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k (p τ))) := by
  obtain ⟨hT0, hcont, -⟩ := id hp
  have hcl : IsClosed {w : ℂ | s ≤ d q w} := by
    have h : {w : ℂ | s ≤ d q w} = {w : ℂ | d q w < s}ᶜ := by
      ext w
      simp [not_lt]
    rw [h]
    exact (isOpen_dBall hd q s).isClosed_compl
  set S : Set ℝ := Icc 0 T ∩ p ⁻¹' {w : ℂ | s ≤ d q w} with hSdef
  have hSc : IsClosed S := hcont.preimage_isClosed_of_isClosed isClosed_Icc hcl
  obtain ⟨τ0, hτ0T, hτ0s⟩ := hexit
  have hSne : S.Nonempty := ⟨τ0, hτ0T, hτ0s⟩
  have hSbdd : BddBelow S := ⟨0, fun τ hτ => hτ.1.1⟩
  have hτ1S : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  obtain ⟨hτ1I, hτ1s⟩ := hτ1S
  have hτ1s' : s ≤ d q (p (sInf S)) := hτ1s
  have hτ1T : sInf S ≤ T := hτ1I.2
  have hin : ∀ τ ∈ Ico 0 (sInf S), d q (p τ) < s := by
    intro τ hτ
    by_contra hcon
    rw [not_lt] at hcon
    have hmem : τ ∈ S := ⟨⟨hτ.1, le_trans hτ.2.le hτ1T⟩, hcon⟩
    have hle : sInf S ≤ τ := csInf_le hSbdd hmem
    linarith [hτ.2]
  have hlen : s - t ≤ sInf S := by
    have h1 := dist_start_le_of_lengthParam hd hp hτ1I
    rw [hx0] at h1
    have h2 := hd.triangle q x (p (sInf S))
    linarith
  have hbound : ∀ τ ∈ Ico 0 (sInf S),
      ENNReal.ofReal (Real.exp Lb) ≤ ENNReal.ofReal (Real.exp (ξ * k (p τ))) := by
    intro τ hτ
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    exact hlow _ (hin τ hτ)
  calc ENNReal.ofReal (Real.exp Lb * (s - t))
      ≤ ENNReal.ofReal (Real.exp Lb) * ENNReal.ofReal (sInf S) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left hlen (Real.exp_nonneg _)
    _ = ∫⁻ _ in Ico 0 (sInf S), ENNReal.ofReal (Real.exp Lb) := by
        rw [setLIntegral_const, Real.volume_Ico, sub_zero]
    _ ≤ ∫⁻ τ in Ico 0 (sInf S), ENNReal.ofReal (Real.exp (ξ * k (p τ))) :=
        setLIntegral_mono' measurableSet_Ico hbound
    _ ≤ ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k (p τ))) :=
        lintegral_mono_set (Ico_subset_Icc_self.trans (Icc_subset_Icc le_rfl hτ1T))

/-- If a length-parametrized curve from `x` (with `d q x < t`) has weighted cost below `e^{Lb} (s - t)`, then it stays in
`{d q · < s}`. -/
theorem inside_of_cost_lt (hd : IsEuclideanLengthMetric d) {ξ Lb s t : ℝ} {q : ℂ} {k : ℂ → ℝ}
    (hlow : ∀ w, d q w < s → Lb ≤ ξ * k w)
    {p : ℝ → ℂ} {T : ℝ} (hp : IsLengthParametrized d p T) {x : ℂ} (hx0 : p 0 = x)
    (hxt : d q x < t)
    (hlt : ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k (p τ))) <
      ENNReal.ofReal (Real.exp Lb * (s - t))) :
    ∀ τ ∈ Icc 0 T, d q (p τ) < s := by
  intro τ hτ
  by_contra hcon
  rw [not_lt] at hcon
  exact absurd (cost_ge_of_exit hd hlow hp hx0 hxt ⟨τ, hτ, hcon⟩) (not_le.mpr hlt)

/-- Two weights which agree on `{d q · < s}` give the same weighted cost to curves inside `{d q · < s}`. -/
theorem lintegral_congr_of_inside {ξ s : ℝ} {q : ℂ} {k1 k2 : ℂ → ℝ} (hsub : ∀ w, d q w < s → k1 w = k2 w)
    {p : ℝ → ℂ} {T : ℝ} (hin : ∀ τ ∈ Icc 0 T, d q (p τ) < s) :
    ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k1 (p τ))) =
      ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k2 (p τ))) := by
  apply setLIntegral_congr_fun measurableSet_Icc
  intro τ hτ
  dsimp only
  rw [hsub _ (hin τ hτ)]

/-- **Local comparison of Weyl distances.** If `k1 = k2` on `{d q · < s}`, the lower bound `ξ k1 ≥ Lb` holds there,
and `d q x < t < s` with `W_{k1}(x, y) < e^{Lb}(s - t)`, then `W_{k2}(x, y) ≤ W_{k1}(x, y)`. -/
theorem weylScaling_le_of_inside (hd : IsEuclideanLengthMetric d) {ξ Lb s t : ℝ} {q : ℂ} {k1 k2 : ℂ → ℝ}
    (hlow : ∀ w, d q w < s → Lb ≤ ξ * k1 w) (hsub : ∀ w, d q w < s → k1 w = k2 w)
    {x y : ℂ} (hxt : d q x < t)
    (hlt : weylScaling d ξ k1 x y < ENNReal.ofReal (Real.exp Lb * (s - t))) :
    weylScaling d ξ k2 x y ≤ weylScaling d ξ k1 x y := by
  by_contra hcon
  rw [not_le] at hcon
  obtain ⟨c, hc1, hc2⟩ := exists_between (lt_min hcon hlt)
  have hcW2 : c < weylScaling d ξ k2 x y := lt_of_lt_of_le hc2 (min_le_left _ _)
  have hcθ : c < ENNReal.ofReal (Real.exp Lb * (s - t)) := lt_of_lt_of_le hc2 (min_le_right _ _)
  have hex : ∃ T p, IsLengthParametrized d p T ∧ p 0 = x ∧ p T = y ∧
      ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k1 (p τ))) < c := by
    have h := hc1
    unfold weylScaling at h
    simp only [iInf_lt_iff, exists_prop] at h
    obtain ⟨T, p, hp, h0, hT, hcost⟩ := h
    exact ⟨T, p, hp, h0, hT, hcost⟩
  obtain ⟨T, p, hp, h0, hT, hcost⟩ := hex
  have hin := inside_of_cost_lt hd hlow hp h0 hxt (lt_trans hcost hcθ)
  have heq := lintegral_congr_of_inside (ξ := ξ) hsub hin
  have hle : weylScaling d ξ k2 x y ≤
      ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k2 (p τ))) := by
    unfold weylScaling
    exact (iInf_le _ T).trans ((iInf_le _ p).trans ((iInf_le _ hp).trans
      ((iInf_le _ h0).trans (iInf_le _ hT))))
  have h3 : ∫⁻ τ in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * k2 (p τ))) < c := by
    rw [← heq]
    exact hcost
  exact absurd (lt_of_le_of_lt hle (lt_trans h3 hcW2)) (lt_irrefl _)

/-- **Short curves.** If `d q x, d q y < t`, `4t ≤ s` and `ξ k ≤ Ub` on `{d q · < s}`, then
`W_k(x, y) ≤ e^{Ub} · 3t`. The curve is an almost-minimizing length-parametrized curve from `x` to `y`; its image
has `d q`-distance `< 4t ≤ s` from `q`. -/
theorem weylScaling_le_short (hd : IsEuclideanLengthMetric d) {ξ Ub s t : ℝ} {q : ℂ} {k : ℂ → ℝ}
    (ht : 0 < t) (hs4 : 4 * t ≤ s) (hup : ∀ w, d q w < s → ξ * k w ≤ Ub) {x y : ℂ}
    (hx : d q x < t) (hy : d q y < t) :
    weylScaling d ξ k x y ≤ ENNReal.ofReal (Real.exp Ub * (3 * t)) := by
  obtain ⟨T, p, hp, h0, hT, hTlt⟩ :=
    exists_lengthParametrized_lt_of_weylScaling_zero (fun a b => hd.weylScaling_zero ξ a b)
      (nonneg_of_length hd) x y ht
  have hxy : d x y < 2 * t := by
    have h1 := hd.triangle x q y
    rw [hd.symm x q] at h1
    linarith
  have hT3 : T < 3 * t := by linarith
  have hin : ∀ τ ∈ Icc 0 T, d q (p τ) < s := by
    intro τ hτ
    have h1 := hd.triangle q x (p τ)
    have h2 := dist_start_le_of_lengthParam hd hp hτ
    rw [h0] at h2
    linarith [hτ.2]
  have hweight : ∀ τ ∈ Icc 0 T, ξ * k (p τ) ≤ Ub := fun τ hτ => hup _ (hin τ hτ)
  have hb := weylScaling_le_of_lengthParametrized d ξ k hp h0 hT hweight
  have hT3' : ENNReal.ofReal T ≤ ENNReal.ofReal (3 * t) := ENNReal.ofReal_le_ofReal hT3.le
  calc weylScaling d ξ k x y
      ≤ ENNReal.ofReal (Real.exp Ub) * ENNReal.ofReal T := hb
    _ ≤ ENNReal.ofReal (Real.exp Ub) * ENNReal.ofReal (3 * t) := mul_le_mul_of_nonneg_left hT3' bot_le
    _ = ENNReal.ofReal (Real.exp Ub * (3 * t)) := (ENNReal.ofReal_mul (Real.exp_pos Ub).le).symm

/-- **Local Weyl equality near a point.** Let `f` be continuous and `f = g` on a Euclidean ball `ball q ρ`. Then there
is `t > 0` such that for all `x, y` in the `d`-ball of radius `t` about `q`, the Weyl distances of `f` and `g` agree and
are finite. -/
theorem weylScaling_eq_near (hd : IsEuclideanLengthMetric d) {ξ : ℝ} {f g : ℂ → ℝ} (hf : Continuous f)
    {q : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hfg : ∀ w ∈ ball q ρ, f w = g w) :
    ∃ t > 0, (∀ x y, d q x < t → d q y < t → weylScaling d ξ f x y = weylScaling d ξ g x y) ∧
      (∀ x y, d q x < t → d q y < t → weylScaling d ξ f x y ≠ ⊤) := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall q ρ).exists_bound_of_continuousOn
    ((continuous_const.mul hf).continuousOn (s := closedBall q ρ))
  have hCb : ∀ w ∈ closedBall q ρ, -C ≤ ξ * f w ∧ ξ * f w ≤ C := fun w hw => by
    have h := hC w hw
    rw [Real.norm_eq_abs] at h
    exact abs_le.mp h
  obtain ⟨ε, hε, hεball⟩ := ((hd.isOpen_iff (ball q ρ)).mp isOpen_ball) q (mem_ball_self hρ)
  set s : ℝ := ε / 2 with hs_def
  have hs : 0 < s := by rw [hs_def]; linarith
  have hsε : ∀ w, d q w < s → w ∈ ball q ρ := fun w hw =>
    hεball w (lt_of_lt_of_le hw (by rw [hs_def]; linarith))
  have hsball : ∀ w, d q w < s → f w = g w := fun w hw => hfg w (hsε w hw)
  have hsC : ∀ w, d q w < s → -C ≤ ξ * f w ∧ ξ * f w ≤ C := fun w hw =>
    hCb w (ball_subset_closedBall (hsε w hw))
  have hmpos : 0 < Real.exp (-C) := Real.exp_pos (-C)
  have hMpos : 0 < Real.exp C := Real.exp_pos C
  set t : ℝ := min (s / 4) (Real.exp (-C) * s / (8 * Real.exp C)) with ht_def
  have ht : 0 < t := lt_min (by linarith) (div_pos (mul_pos hmpos hs) (by positivity))
  have ht4 : t ≤ s / 4 := min_le_left _ _
  have htM : t ≤ Real.exp (-C) * s / (8 * Real.exp C) := min_le_right _ _
  have hs4 : 4 * t ≤ s := by linarith
  have hst : 0 < s - t := by linarith
  have hθpos : 0 < Real.exp (-C) * (s - t) := mul_pos hmpos hst
  have hkey : Real.exp C * (3 * t) < Real.exp (-C) * (s - t) := by
    have h1 : t * (8 * Real.exp C) ≤ Real.exp (-C) * s := by
      have := htM
      rw [le_div_iff₀ (by positivity)] at this
      exact this
    have h2 : Real.exp (-C) * t ≤ Real.exp (-C) * (s / 4) :=
      mul_le_mul_of_nonneg_left ht4 hmpos.le
    have h3 : Real.exp (-C) * (s - t) = Real.exp (-C) * s - Real.exp (-C) * t := by ring
    have h4 : 0 < Real.exp (-C) * s := mul_pos hmpos hs
    rw [h3]
    nlinarith
  have hlt_f : ∀ x y, d q x < t → d q y < t →
      weylScaling d ξ f x y < ENNReal.ofReal (Real.exp (-C) * (s - t)) := by
    intro x y hx hy
    refine lt_of_le_of_lt (weylScaling_le_short hd ht hs4 (fun w hw => (hsC w hw).2) hx hy) ?_
    rw [ENNReal.ofReal_lt_ofReal_iff hθpos]
    exact hkey
  have hlt_g : ∀ x y, d q x < t → d q y < t →
      weylScaling d ξ g x y < ENNReal.ofReal (Real.exp (-C) * (s - t)) := by
    intro x y hx hy
    refine lt_of_le_of_lt (weylScaling_le_short (k := g) (Ub := C) hd ht hs4 (fun w hw => ?_) hx hy) ?_
    · rw [← hsball w hw]
      exact (hsC w hw).2
    · rw [ENNReal.ofReal_lt_ofReal_iff hθpos]
      exact hkey
  refine ⟨t, ht, fun x y hx hy => le_antisymm ?_ ?_, fun x y hx hy => ne_top_of_lt (hlt_f x y hx hy)⟩
  · exact weylScaling_le_of_inside hd (k1 := g) (k2 := f)
      (fun w hw => by rw [← hsball w hw]; exact (hsC w hw).1) (fun w hw => (hsball w hw).symm) hx
      (hlt_g x y hx hy)
  · exact weylScaling_le_of_inside hd (k1 := f) (k2 := g)
      (fun w hw => (hsC w hw).1) hsball hx (hlt_f x y hx hy)

end RootedLocal

end HarmonicBalls

