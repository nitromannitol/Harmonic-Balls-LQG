import HarmonicBalls.FirstPass.S11r.RootedLocality
import HarmonicBalls.FirstPass.S11m.WeylLengthCompact
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.WeylPathReverse
import HarmonicBalls.Steps.Sec11.PinchInequalities

/-!
# Localization of internal metrics by an exit cost

For a function `e : ℂ → ℂ → ℝ`, open sets `V ⊆ D` and two points `u, v`: if every path from `u` to `v` which leaves
`V` has `e`-length at least `κ`, and the internal metric `e(u, v; V)` is smaller than `κ`, then
`e(u, v; D) = e(u, v; V)` (`internalMetric_eq_of_exit_cost`). Near-optimal paths in `D` cannot leave `V`.

The main application is to Weyl scalings `e = e^{ξ k} · d` (Gwynne-Miller, arXiv:1905.00383v3, §1.2, eq. (1.8)) of a
Euclidean length metric `d` by a weight `k` which may be singular away from `V` (for instance
`k = -α log |·| - γ log |· - z|` with `0, z ∉ V`): when `k` agrees on `V` with a continuous compactly supported `f`,
the internal metrics of `(e^{ξ k} · d)` on `D` and on `V` agree for all pairs of points near any `q ∈ V`
(`internalMetric_weylScaling_eq_near`). The exit cost comes from the lower bound of the weight on a small `d`-ball
around `q` (`RootedLocal.cost_ge_of_exit`), and the smallness from the continuity of the internal metric of the
Euclidean length metric `e^{ξ f} · d` on `V`, which agrees with that of `e^{ξ k} · d` on `V`
(`RootedLocal.internalMetric_weylScaling_eq_of_eventuallyEq`). No property of `k` outside `V` is used.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace RootedLocal

/-- One-step partition bound: for any `e`, any path `P` from `w` and any `t ∈ [0, 1]`,
`e(P(t), w) ≤ len(P; e)`. -/
theorem ofReal_le_pathLength_extend (e : ℂ → ℂ → ℝ) {w x : ℂ} (P : Path w x) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (e (P.extend t) w) ≤ pathLength e P := by
  have hmono : Monotone (fun i : ℕ => if i = 0 then (0 : ℝ) else t) := by
    intro i j hij
    by_cases hi : i = 0
    · by_cases hj : j = 0
      · simp [hi, hj]
      · simp [hi, hj, ht.1]
    · have hj : j ≠ 0 := by omega
      simp [hi, hj]
  have hmem : ∀ i, (fun i : ℕ => if i = 0 then (0 : ℝ) else t) i ∈ Icc (0 : ℝ) 1 := by
    intro i
    by_cases hi : i = 0
    · simp [hi]
    · simpa [hi] using ht
  unfold pathLength curveLength
  refine le_trans (le_of_eq ?_) (le_iSup (fun q : ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1 } =>
    ∑ i ∈ Finset.range q.1, ENNReal.ofReal (e (P.extend (q.2.1 (i + 1))) (P.extend (q.2.1 i))))
    (1, ⟨_, hmono, hmem⟩))
  simp

/-- Localization by an exit cost: if every path from `u` to `v` leaving `V` has `e`-length at least `κ` and
`e(u, v; V) < κ`, then `e(u, v; D) = e(u, v; V)` for every `D ⊇ V`. -/
theorem internalMetric_eq_of_exit_cost {e : ℂ → ℂ → ℝ} {V D : Set ℂ} (hVD : V ⊆ D) {u v : ℂ}
    {κ : ℝ≥0∞} (hexit : ∀ P : Path u v, (∃ t, P t ∉ V) → κ ≤ pathLength e P)
    (hsmall : internalMetric e V u v < κ) :
    internalMetric e D u v = internalMetric e V u v := by
  refine le_antisymm (internalMetric_anti e hVD u v) ?_
  show internalMetric e V u v ≤ ⨅ (P : Path u v) (_ : ∀ t, P t ∈ D), pathLength e P
  refine le_iInf₂ fun P _ => ?_
  by_cases hin : ∀ t, P t ∈ V
  · exact iInf₂_le (f := fun (P : Path u v) (_ : ∀ t, P t ∈ V) => pathLength e P) P hin
  · simp only [not_forall] at hin
    exact (hsmall.trans_le (hexit P hin)).le

variable {d : ℂ → ℂ → ℝ}

/-- Internal metrics of a Weyl scaling `e^{ξ k} · d` on `D` and on an open connected `V ⊆ D` agree near every point
of `V`, when `k` agrees on `V` with a continuous compactly supported weight `f`. The weight `k` is arbitrary outside
`V` (it may be singular there). -/
theorem internalMetric_weylScaling_eq_near (hd : IsEuclideanLengthMetric d) {ξ : ℝ}
    {f k : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {V D : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V) (hVD : V ⊆ D)
    (hfk : ∀ w ∈ V, f w = k w) {q : ℂ} (hq : q ∈ V) :
    ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      internalMetric (fun a b => (weylScaling d ξ k a b).toReal) D u v =
        internalMetric (fun a b => (weylScaling d ξ k a b).toReal) V u v := by
  -- a Euclidean ball around `q` inside `V`
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.mp hV q hq
  -- the two Weyl scalings agree, and are finite, on a small `d`-ball around `q`
  obtain ⟨t, ht, heq, hfin⟩ := weylScaling_eq_near (ξ := ξ) hd hf hρ (fun w hw => hfk w (hρV hw))
  -- a `d`-ball around `q` inside the Euclidean ball
  obtain ⟨ε, hε, hεball⟩ := (hd.isOpen_iff (ball q ρ)).mp isOpen_ball q (mem_ball_self hρ)
  -- a bound for `ξ f` on the closed Euclidean ball
  obtain ⟨C, hC⟩ := (isCompact_closedBall q ρ).exists_bound_of_continuousOn
    ((continuous_const.mul hf).continuousOn (s := closedBall q ρ))
  obtain ⟨s, hs, hst, hsε⟩ : ∃ s : ℝ, 0 < s ∧ s < t ∧ s < ε :=
    ⟨min t ε / 2, half_pos (lt_min ht hε), (half_lt_self (lt_min ht hε)).trans_le (min_le_left _ _),
      (half_lt_self (lt_min ht hε)).trans_le (min_le_right _ _)⟩
  have hlow : ∀ w, d q w < s → -C ≤ ξ * k w := by
    intro w hw
    have hwρ : w ∈ ball q ρ := hεball w (hw.trans hsε)
    rw [← hfk w (hρV hwρ)]
    have h := hC w (ball_subset_closedBall hwρ)
    rw [Real.norm_eq_abs] at h
    exact (abs_le.mp h).1
  set κ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-C) * (s - s / 2)) with hκ_def
  have hκ : 0 < κ := ENNReal.ofReal_pos.mpr (mul_pos (Real.exp_pos _) (by linarith))
  -- exit cost of a single step from `u` (inside the `d`-ball of radius `s/2`) to the `d`-sphere of radius `s`
  have hcost : ∀ u y, d q u < s / 2 → d q y = s →
      κ ≤ ENNReal.ofReal ((weylScaling d ξ k y u).toReal) := by
    intro u y hu hy
    have hfinuy : weylScaling d ξ k u y ≠ ⊤ := by
      rw [← heq u y (by linarith) (by linarith)]
      exact hfin u y (by linarith) (by linarith)
    have hle : κ ≤ weylScaling d ξ k u y := by
      unfold weylScaling
      refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun hp0 => le_iInf fun hpT => ?_
      exact cost_ge_of_exit hd hlow hp hp0 hu ⟨T, ⟨hp.1, le_rfl⟩, by rw [hpT]; exact hy.ge⟩
    rw [hd.weylScaling_symm ξ k y u, ENNReal.ofReal_toReal hfinuy]
    exact hle
  -- exit cost of a whole path leaving `V`
  have hexit : ∀ u v, d q u < s / 2 → ∀ P : Path u v, (∃ τ, P τ ∉ V) →
      κ ≤ pathLength (fun a b => (weylScaling d ξ k a b).toReal) P := by
    intro u v hu P ⟨τ, hτ⟩
    have hτs : s ≤ d q (P τ) := by
      by_contra hlt
      exact hτ (hρV (hεball _ ((not_le.mp hlt).trans hsε)))
    have hcont : ContinuousOn (fun r : ℝ => d (P.extend r) q) (Icc 0 (τ : ℝ)) :=
      ((hd.continuous_left q).comp P.continuous_extend).continuousOn
    have h0 : d (P.extend 0) q ≤ s := by
      rw [P.extend_zero, hd.symm]
      linarith
    have h1 : s ≤ d (P.extend τ) q := by
      rw [P.extend_extends', hd.symm]
      exact hτs
    obtain ⟨r, hr, hrs⟩ := intermediate_value_Icc τ.2.1 hcont ⟨h0, h1⟩
    have hr01 : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1, hr.2.trans τ.2.2⟩
    calc κ ≤ ENNReal.ofReal ((weylScaling d ξ k (P.extend r) u).toReal) :=
          hcost u _ hu (by rw [hd.symm]; exact hrs)
      _ ≤ pathLength (fun a b => (weylScaling d ξ k a b).toReal) P :=
          ofReal_le_pathLength_extend (fun a b => (weylScaling d ξ k a b).toReal) P hr01
  -- smallness of the internal metric on `V` near `(q, q)`
  obtain ⟨-, hFL⟩ := weylScaling_continuous_compactSupport_length d ξ f hd hf hfc
  have hFnn : ∀ x y, 0 ≤ (fun a b => (weylScaling d ξ f a b).toReal) x y :=
    fun _ _ => ENNReal.toReal_nonneg
  have hcontF := hFL.continuousAt_internalMetric_pair hFnn hV hq hq
  have hself := hFL.internalMetric_self_of_mem_open hFnn hV hq
  have hlt : (fun p : ℂ × ℂ => internalMetric (fun a b => (weylScaling d ξ f a b).toReal) V p.1 p.2) (q, q)
      < κ := by
    simpa only [hself] using hκ
  obtain ⟨s₂, hs₂, hs₂sub⟩ := Metric.mem_nhds_iff.mp (hcontF (Iio_mem_nhds hlt))
  have hq3 : q ∈ {w | d q w < s / 2} := by
    show d q q < s / 2
    rw [hd.self_eq_zero]
    linarith
  obtain ⟨s₃, hs₃, hs₃sub⟩ := Metric.isOpen_iff.mp (isOpen_dBall hd q (s / 2)) q hq3
  refine ⟨min s₂ s₃, lt_min hs₂ hs₃, fun u hu v hv => ?_⟩
  have hu3 : d q u < s / 2 := hs₃sub (ball_subset_ball (min_le_right _ _) hu)
  have huv : (u, v) ∈ ball (q, q) s₂ := by
    rw [← ball_prod_same]
    exact ⟨ball_subset_ball (min_le_left _ _) hu, ball_subset_ball (min_le_left _ _) hv⟩
  have hsm : internalMetric (fun a b => (weylScaling d ξ f a b).toReal) V u v < κ := hs₂sub huv
  have hEF : internalMetric (fun a b => (weylScaling d ξ k a b).toReal) V u v =
      internalMetric (fun a b => (weylScaling d ξ f a b).toReal) V u v :=
    internalMetric_weylScaling_eq_of_eventuallyEq hd hf hfc hV hVc
      (fun x hx => Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hfk)
  exact internalMetric_eq_of_exit_cost hVD (hexit u v hu3) (hEF ▸ hsm)

end RootedLocal

end HarmonicBalls
