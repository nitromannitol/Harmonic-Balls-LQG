import HarmonicBalls.FirstPass.Phase2.InternalMetricExitLocalization
import HarmonicBalls.FirstPass.S11r.RootedRootContinuity
import HarmonicBalls.FirstPass.S11r.VIdentity

/-!
# The internal metric of the rooted Weyl scaling tends to `0` at the diagonal

For a Euclidean length metric `d`, the weight `k_z = -α log |·| - γ log |· - z| + γ log max (1, |·|)` of the rooted
field and a disk `D = ball c r` with `closedBall c r ⊆ ball 0 1` and `0 ∉ closedBall c r`, the internal metric
`E = internalMetric (weylPhysicalE d ξ k_z) D` of the Weyl scaling `e^{ξ k_z} · d` satisfies `E(u, p) → 0` as `u → p`
within `D`, for every `p ∈ D`:

* for `p ≠ z`, the weight agrees near `p` with a smooth compactly supported weight (`exists_rooted_cutoff`), so the
  localization `RootedLocal.internalMetric_weylScaling_eq_near` and the continuity of the internal metric of the
  Euclidean length metric of the cutoff weight apply
  (`RootedLocal.tendsto_internalMetric_weylScaling_of_mem_open`);
* for `p = z`, the continuity of the Weyl distance at the insertion gives `E(u, z) ≤ W(u, z)` near `z`
  (`internalMetric_le_weylScaling_eventually`).

Terminology: Weyl scaling `e^{ξ f} · d` (Duplantier-Sheffield; Gwynne-Miller), internal metric `D(·,·;U)`
(Armstrong-Kuusi-Mourrat).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace RootedLocal

/-- **Diagonal continuity of a localized Weyl internal metric.** If a weight `k` agrees on an open connected
`V ⊆ D` with a continuous compactly supported weight `f`, then the internal metric on `D` of the Weyl scaling
`e^{ξ k} · d` tends to `0` at `q ∈ V`: `E(u, q) → 0` as `u → q`. The weight `k` is arbitrary outside `V`. -/
theorem tendsto_internalMetric_weylScaling_of_mem_open {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) {ξ : ℝ}
    {f k : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {V D : Set ℂ} (hV : IsOpen V) (hVc : IsConnected V) (hVD : V ⊆ D)
    (hfk : ∀ w ∈ V, f w = k w) {q : ℂ} (hq : q ∈ V) :
    Tendsto (fun u => internalMetric (fun a b => (weylScaling d ξ k a b).toReal) D u q) (𝓝 q) (𝓝 0) := by
  obtain ⟨s, hs, hloc⟩ := internalMetric_weylScaling_eq_near hd hf hfc hV hVc hVD hfk hq
  obtain ⟨-, hFL⟩ := weylScaling_continuous_compactSupport_length d ξ f hd hf hfc
  have hFnn : ∀ x y, 0 ≤ (fun a b => (weylScaling d ξ f a b).toReal) x y :=
    fun _ _ => ENNReal.toReal_nonneg
  have hcontF := hFL.continuousAt_internalMetric_pair hFnn hV hq hq
  have hself := hFL.internalMetric_self_of_mem_open hFnn hV hq
  have hpair : Tendsto (fun u : ℂ => (u, q)) (𝓝 q) (𝓝 (q, q)) :=
    (continuous_id.prodMk continuous_const).tendsto q
  have h1 : Tendsto (fun u => internalMetric (fun a b => (weylScaling d ξ f a b).toReal) V u q) (𝓝 q) (𝓝 0) := by
    have h := hcontF.tendsto.comp hpair
    simpa only [Function.comp_def, hself] using h
  have hEF : ∀ u v, internalMetric (fun a b => (weylScaling d ξ k a b).toReal) V u v =
      internalMetric (fun a b => (weylScaling d ξ f a b).toReal) V u v := fun u v =>
    internalMetric_weylScaling_eq_of_eventuallyEq hd hf hfc hV hVc
      (fun x hx => Filter.eventuallyEq_of_mem (hV.mem_nhds hx) hfk)
  refine Tendsto.congr' ?_ (h1.congr fun u => (hEF u q).symm)
  filter_upwards [ball_mem_nhds q hs] with u hu
  exact (hloc u hu q (mem_ball_self hs)).symm

end RootedLocal

/-- **Diagonal continuity of the internal metric of the rooted Weyl scaling.** Let `d` be a Euclidean length metric,
`D = ball c r` with `closedBall c r ⊆ ball 0 1` and `0 ∉ closedBall c r`, `z ∈ D`, and assume the Weyl distance
`W(x, z) = weylScaling d ξ k_z x z` tends to `0` as `x → z`, where
`k_z = -α log |·| - γ log |· - z| + γ log max (1, |·|)`. Then for every `p ∈ D` the internal metric
`E = internalMetric (weylPhysicalE d ξ k_z) D` of the Weyl scaling satisfies `E(u, p) → 0` as `u → p` within `D`
(in `ℝ≥0∞`). -/
theorem tendsto_internalMetric_rootedWeight_diag {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (ξ α γ : ℝ) {c : ℂ} {r : ℝ} (hcD : closedBall c r ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r)
    {z : ℂ} (hz : z ∈ ball c r)
    (hW : Tendsto (fun x => weylScaling d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) x z) (𝓝 z) (𝓝 0)) :
    ∀ p ∈ ball c r, Tendsto (fun u => internalMetric (weylPhysicalE d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) (ball c r) u p)
      (𝓝[ball c r] p) (𝓝 0) := by
  intro p hp
  by_cases hpz : p = z
  · subst hpz
    have hfc : ContinuousOn
        (fun w : ℂ => -α * Real.log ‖w‖ - γ * Real.log ‖w - p‖ + γ * Real.log (max 1 ‖w‖))
        (ball c r \ {p}) := by
      have h0' : ∀ w ∈ ball c r \ {p}, ‖w‖ ≠ 0 := fun w hw =>
        norm_ne_zero_iff.2 fun hw0 => h0 (hw0 ▸ ball_subset_closedBall hw.1)
      have h1' : ∀ w ∈ ball c r \ {p}, ‖w - p‖ ≠ 0 := fun w hw =>
        norm_ne_zero_iff.2 (sub_ne_zero.2 hw.2)
      have h2' : ∀ w ∈ ball c r \ {p}, max 1 ‖w‖ ≠ 0 := fun w _ =>
        (lt_max_of_lt_left one_pos).ne'
      exact ((continuousOn_const.mul (continuous_norm.continuousOn.log h0')).sub
        (continuousOn_const.mul ((continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn.log h1'))).add
        (continuousOn_const.mul ((continuous_const.max continuous_norm).continuousOn.log h2'))
    have hkey := internalMetric_le_weylScaling_eventually hd ξ isOpen_ball hz hfc hW
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (hW.mono_left nhdsWithin_le_nhds) (Eventually.of_forall fun _ => zero_le)
      (nhdsWithin_le_nhds hkey)
  · -- a small ball around `p` inside the disk and away from `z`
    have hpc : dist p c < r := mem_ball.1 hp
    have hδ : 0 < min (dist z p) (r - dist p c) :=
      lt_min (dist_pos.2 (Ne.symm hpz)) (by linarith)
    set δ := min (dist z p) (r - dist p c) with hδdef
    have hδz : δ ≤ dist z p := min_le_left _ _
    have hδr : δ ≤ r - dist p c := min_le_right _ _
    have hcb : closedBall p (δ / 2) ⊆ ball c r := by
      intro w hw
      have h1 := mem_closedBall.1 hw
      have h2 := dist_triangle w p c
      rw [mem_ball]
      linarith
    have hcb' : closedBall p (δ / 2) ⊆ ball (0 : ℂ) 1 := fun w hw =>
      hcD (ball_subset_closedBall (hcb hw))
    have h0p : (0 : ℂ) ∉ closedBall p (δ / 4) := fun h =>
      h0 (ball_subset_closedBall (hcb (closedBall_subset_closedBall (by linarith) h)))
    obtain ⟨g, hgd, hgc, -, hgv⟩ := exists_rooted_cutoff α γ (c := p) (z := z) (r := δ / 4) (R := δ / 2)
      (by linarith) (by linarith) (by linarith) hcb' h0p
    have hfk : ∀ w ∈ ball p (δ / 4), g w =
        -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖) := by
      intro w hw
      have hw1 : ‖w‖ < 1 := by
        have := hcb' (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hw))
        simpa using this
      rw [hgv w hw, max_eq_left hw1.le, Real.log_one]
      ring
    have hV : p ∈ ball p (δ / 4) := mem_ball_self (by linarith)
    have hlim := RootedLocal.tendsto_internalMetric_weylScaling_of_mem_open (D := ball c r) hd (ξ := ξ)
      hgd.continuous hgc (isOpen_ball)
      ((convex_ball p (δ / 4)).isConnected ⟨p, hV⟩)
      (fun w hw => hcb (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hw))) hfk hV
    exact hlim.mono_left nhdsWithin_le_nhds

end HarmonicBalls
