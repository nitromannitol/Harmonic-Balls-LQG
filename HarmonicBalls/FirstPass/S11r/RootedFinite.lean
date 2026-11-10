import HarmonicBalls.FirstPass.S11r.RootedPhysical
import HarmonicBalls.FirstPass.S11m.Finiteness
import HarmonicBalls.Steps.Sec11.WeylLocalEdges
import HarmonicBalls.Steps.Sec11.CurveLengthReparam
import HarmonicBalls.Steps.Sec11.MetricArcLength
import HarmonicBalls.Steps.Sec11.WeylPathReverse
import HarmonicBalls.Steps.Sec11.WeylPathConcatenation

/-!
# First pass, finiteness of the Weyl-scaled physical metric on a disk (fp-S11r, owner n2; R2 Step B-C-G)

Deterministic finiteness for the physical metric `e := fun a b => (weylScaling d ξ f a b).toReal` of the rooted field,
on an open connected set `D` where the weight `exp (ξ f)` is bounded (CHATGPT-n2-R2-rooted-length.md section 3, Steps
B-C-G). The weight `f` is only bounded on `D`, so the arclength reparametrization of a competitor must stay in `D`:
its image is the image of the curve (`cumulative_curveLength_properties`: the cumulative length maps `[0, T]` onto
`[0, L]`), which lies in `D`.

* `weylScaling_le_mul_curveLength_core`: for a curve on `[0, T]` in `D` of finite `d`-length, the Weyl cost of its
  endpoints is at most `M` times its `d`-length (Fact 2.2 III comparison, arclength reparametrization).
* `weylScaling_le_mul_curveLength_of_subset`: the same on `[a, b]` (translation).
* `pathLength_weylScaling_toReal_le`: the `e`-length of a path in `D` is at most `M` times its `d`-length.
* `internalMetric_weylScaling_toReal_ne_top`: the internal metric of `e` on `D` is finite on `D × D`.
* `exists_expWeight_bound`: a continuous weight is bounded on a compact set.

Conventions: `d` is a Euclidean length metric (`IsEuclideanLengthMetric`, Defs/LQGMetric.lean); in the rooted gluing `d` is
`𝔇 (hC ω)`, which is a length metric almost surely (`SatisfiesLQGMetricAxioms.ae_isEuclideanLengthMetric`).
-/

namespace HarmonicBalls

open Set Filter Topology Metric
open scoped ENNReal

/-- Weyl cost of the endpoints of a curve on `[0, T]` lying in `D`, bounded by `M` times its `d`-length. -/
theorem weylScaling_le_mul_curveLength_core {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (ξ : ℝ) {f : ℂ → ℝ} {D : Set ℂ} {M : ℝ} (hM : 0 < M) (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M)
    {p : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T) (hp : ContinuousOn p (Icc 0 T)) (hpD : ∀ t ∈ Icc 0 T, p t ∈ D)
    (hfin : curveLength d p 0 T < ⊤) :
    weylScaling d ξ f (p 0) (p T) ≤ ENNReal.ofReal M * curveLength d p 0 T := by
  obtain ⟨q, hq, hq0, hqT, hqt⟩ := IsEuclideanLengthMetric.exists_lengthParametrized_with_tracking hd hT hp hfin
  obtain ⟨-, -, -, hsurj⟩ := IsEuclideanLengthMetric.cumulative_curveLength_properties hd hT hp hfin
  have hweight : ∀ s ∈ Icc 0 (curveLength d p 0 T).toReal, ξ * f (q s) ≤ Real.log M := by
    intro s hs
    have hs' : s ∈ (fun t => (curveLength d p 0 t).toReal) '' Icc 0 T := by
      rw [hsurj]
      exact hs
    obtain ⟨t, ht, rfl⟩ := hs'
    show ξ * f (q (curveLength d p 0 t).toReal) ≤ Real.log M
    rw [hqt t ht]
    have h := Real.log_le_log (Real.exp_pos _) (hfM (p t) (hpD t ht))
    rwa [Real.log_exp] at h
  have hb := weylScaling_le_of_lengthParametrized d ξ f hq hq0 hqT hweight
  rw [Real.exp_log hM, ENNReal.ofReal_toReal hfin.ne] at hb
  exact hb

/-- Weyl cost bound on a general interval `[a, b]`: translate the curve to start at `0`. -/
theorem weylScaling_le_mul_curveLength_of_subset {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (ξ : ℝ) {f : ℂ → ℝ} {D : Set ℂ} {M : ℝ} (hM : 0 < M) (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M)
    {p : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b) (hp : ContinuousOn p (Icc a b)) (hpD : ∀ t ∈ Icc a b, p t ∈ D)
    (hfin : curveLength d p a b < ⊤) :
    weylScaling d ξ f (p a) (p b) ≤ ENNReal.ofReal M * curveLength d p a b := by
  have hgc : ContinuousOn (fun τ => p (τ + a)) (Icc 0 (b - a)) := by
    apply hp.comp (continuous_id.add continuous_const).continuousOn
    intro τ hτ
    show τ + a ∈ Icc a b
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hgD : ∀ τ ∈ Icc 0 (b - a), p (τ + a) ∈ D :=
    fun τ hτ => hpD _ ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have htr := IsEuclideanLengthMetric.curveLength_translate hd p (-a) 0 (b - a)
  simp only [sub_neg_eq_add, zero_add, sub_add_cancel] at htr
  have hgfin : curveLength d (fun τ => p (τ + a)) 0 (b - a) < ⊤ := by
    rw [htr]
    exact hfin
  have key := weylScaling_le_mul_curveLength_core hd ξ hM hfM (sub_nonneg.2 hab) hgc hgD hgfin
  simp only [zero_add, sub_add_cancel] at key
  rw [htr] at key
  exact key

/-- The `e`-length of a path in `D` is at most `M` times its `d`-length, where `e = (weylScaling d ξ f ·  ·).toReal`. -/
theorem pathLength_weylScaling_toReal_le {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (ξ : ℝ) {f : ℂ → ℝ} {D : Set ℂ} {M : ℝ} (hM : 0 < M) (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M)
    {x y : ℂ} (P : Path x y) (hP : ∀ t, P t ∈ D) (hfin : pathLength d P < ⊤) :
    pathLength (fun a b => (weylScaling d ξ f a b).toReal) P ≤ ENNReal.ofReal M * pathLength d P := by
  have hPD : ∀ t ∈ Icc (0 : ℝ) 1, P.extend t ∈ D := by
    intro t ht
    have e1 : P.extend t = P ⟨t, ht⟩ := Path.extend_extends' P ⟨t, ht⟩
    rw [e1]
    exact hP _
  have hfin0 : curveLength d P.extend 0 1 < ⊤ := hfin
  have hpiece : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      weylScaling d ξ f (P.extend a) (P.extend b) ≤ ENNReal.ofReal M * curveLength d P.extend a b := by
    intro a b ha hab hb
    refine weylScaling_le_mul_curveLength_of_subset hd ξ hM hfM hab ?_ (fun t ht => hPD t ⟨ha.trans ht.1, ht.2.trans hb⟩) ?_
    · exact P.continuous_extend.continuousOn.mono (Icc_subset_Icc ha hb)
    · exact lt_of_le_of_lt (curveLength_mono_interval d P.extend ha hb) hfin0
  unfold pathLength
  conv_lhs => unfold curveLength
  refine iSup_le fun w => ?_
  rcases w with ⟨N, u, hu, hmem⟩
  have hterm : ∀ i ∈ Finset.range N,
      ENNReal.ofReal ((weylScaling d ξ f (P.extend (u (i + 1))) (P.extend (u i))).toReal)
        ≤ ENNReal.ofReal M * curveLength d P.extend (u i) (u (i + 1)) := by
    intro i _
    have h1 := hpiece (u i) (u (i + 1)) (hmem i).1 (hu (Nat.le_succ i)) (hmem (i + 1)).2
    have hfinW : weylScaling d ξ f (P.extend (u (i + 1))) (P.extend (u i)) ≠ ⊤ := by
      rw [IsEuclideanLengthMetric.weylScaling_symm hd ξ f]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) h1
      exact (lt_of_le_of_lt (curveLength_mono_interval d P.extend (hmem i).1 (hmem (i + 1)).2) hfin0).ne
    rw [ENNReal.ofReal_toReal hfinW, IsEuclideanLengthMetric.weylScaling_symm hd ξ f]
    exact h1
  calc ∑ i ∈ Finset.range N, ENNReal.ofReal ((weylScaling d ξ f (P.extend (u (i + 1))) (P.extend (u i))).toReal)
      ≤ ∑ i ∈ Finset.range N, ENNReal.ofReal M * curveLength d P.extend (u i) (u (i + 1)) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal M * ∑ i ∈ Finset.range N, curveLength d P.extend (u i) (u (i + 1)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal M * curveLength d P.extend (u 0) (u N) :=
        mul_le_mul_of_nonneg_left (S11m.sum_curveLength_le d P.extend hu N) (zero_le)
    _ ≤ ENNReal.ofReal M * curveLength d P.extend 0 1 :=
        mul_le_mul_of_nonneg_left (curveLength_mono_interval d P.extend (hmem 0).1 (hmem N).2) (zero_le)

/-- **Finiteness (Steps B-C-G).** On an open connected `D` where `exp (ξ f) ≤ M`, the internal metric of the Weyl-scaled
physical metric `e = (weylScaling d ξ f ·  ·).toReal` is finite on `D × D`. Proof: a path in `D` of finite `d`-length
exists (`internalMetric_ne_top_of_isConnected`), and its `e`-length is at most `M` times its `d`-length. -/
theorem internalMetric_weylScaling_toReal_ne_top {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (ξ : ℝ) {f : ℂ → ℝ} {D : Set ℂ} (hD : IsOpen D) (hDc : IsConnected D) {M : ℝ} (hM : 0 < M)
    (hfM : ∀ z ∈ D, Real.exp (ξ * f z) ≤ M) {x y : ℂ} (hx : x ∈ D) (hy : y ∈ D) :
    internalMetric (fun a b => (weylScaling d ξ f a b).toReal) D x y ≠ ⊤ := by
  have hlt : internalMetric d D x y < ⊤ :=
    lt_top_iff_ne_top.2 (S11m.internalMetric_ne_top_of_isConnected hd hD hDc hx hy)
  unfold internalMetric at hlt
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hPD, hPlt⟩ := iInf_lt_iff.1 hP
  have h2 : internalMetric (fun a b => (weylScaling d ξ f a b).toReal) D x y ≤
      pathLength (fun a b => (weylScaling d ξ f a b).toReal) P := by
    unfold internalMetric
    exact iInf₂_le P hPD
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPlt.ne)
    (h2.trans (pathLength_weylScaling_toReal_le hd ξ hM hfM P hPD hPlt))

/-- A continuous weight is bounded on a compact set: `exp (ξ f) ≤ M` there, for some `M > 0`. -/
theorem exists_expWeight_bound {f : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K) (hf : ContinuousOn f K) (ξ : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ z ∈ K, Real.exp (ξ * f z) ≤ M := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf
  refine ⟨Real.exp (|ξ| * C), Real.exp_pos _, fun z hz => Real.exp_le_exp.2 ?_⟩
  calc ξ * f z ≤ |ξ * f z| := le_abs_self _
    _ = |ξ| * |f z| := abs_mul _ _
    _ ≤ |ξ| * C := mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hC z hz) (abs_nonneg ξ)

end HarmonicBalls
