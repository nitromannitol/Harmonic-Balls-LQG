import HarmonicBalls.FirstPass.S11u.Kernel
import HarmonicBalls.LPStage.GFFExistence

/-!
# Constructed whole-plane GFF: covariance of circle averages and the increment variance bound (HB level)

Owner: worker z6, task fp-phase2-gff-existence-row29. Lemmas about the covariance kernel `wholePlaneGFFCov` on pairs of
circle averages with different centers and radii, the input of the moment bound of MQ-lh-17 (B4).

* `wholePlaneGFFCov_circle_circle_eq`: the cross covariance of circle averages is the mean value identity
  `Cov(h_r(z), h_s(w)) = A_r(z) + A_s(w) - avg_{x in ∂B_r(z)} log max(s, |x - w|)`, where `A_r(z)` is the average of
  `log max(|·|, 1)` over `∂B_r(z)`. The mean value identity is `circleAverage_wholePlaneCov` (S11u/Kernel.lean:42), the
  Jensen formula of Duplantier-Sheffield (arXiv:0808.1560 Section 3.1) and Armitage-Gardiner (potential theory).
* `wholePlaneGFFCov_circle_self_eq`: the variance `Var(h_r(z)) = 2 A_r(z) - log r`.
* `wholePlaneGFFCov_circle_increment_le`: the variance of `h_r(z) - h_s(w)` is at most
  `2 log(max r s + |z - w|) - log r - log s ≤ (|r - s| + 2 |z - w|) / a` for `a ≤ r, s` (MQ-lh-17 (b)).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric Topology

/-- Continuity of `logMaxAbs` (the average of `log max(|·|, 1)` is then a continuous integrand on circles). -/
lemma continuous_logMaxAbs : Continuous logMaxAbs := by
  unfold logMaxAbs
  exact (continuous_norm.max continuous_const).log
    (fun x => ((lt_of_lt_of_le one_pos (le_max_right _ _)).ne'))

/-- A continuous real function is circle integrable on every circle. -/
lemma circleIntegrable_of_continuous {f : ℂ → ℝ} (hf : Continuous f) (c : ℂ) (R : ℝ) :
    CircleIntegrable f c R :=
  hf.continuousOn.circleIntegrable'

/-- Cross covariance of two circle averages (mean value identity, Duplantier-Sheffield Section 3.1). -/
theorem wholePlaneGFFCov_circle_circle_eq {r s : ℝ} (hs : 0 < s) (z w : ℂ) :
    wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle s w) =
      Real.circleAverage logMaxAbs z r + Real.circleAverage logMaxAbs w s
        - Real.circleAverage (fun x : ℂ => Real.log (max s ‖x - w‖)) z r := by
  unfold wholePlaneGFFCov
  simp only [GFFObservable.smear]
  have hfun : (fun x : ℂ => Real.circleAverage (fun y => wholePlaneCov x y) w s) =
      (logMaxAbs + fun _ : ℂ => Real.circleAverage logMaxAbs w s) -
        (fun x : ℂ => Real.log (max s ‖x - w‖)) := by
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [circleAverage_wholePlaneCov hs]
  have hcL : Continuous logMaxAbs := continuous_logMaxAbs
  have hcLog : Continuous (fun x : ℂ => Real.log (max s ‖x - w‖)) :=
    (continuous_const.max (continuous_id.sub continuous_const).norm).log
      (fun x => (lt_of_lt_of_le hs (le_max_left _ _)).ne')
  rw [hfun, Real.circleAverage_sub
      (circleIntegrable_of_continuous (hcL.add continuous_const) _ _)
      (circleIntegrable_of_continuous hcLog _ _),
    Real.circleAverage_add (circleIntegrable_of_continuous hcL _ _)
      (circleIntegrable_of_continuous continuous_const _ _),
    Real.circleAverage_const]

/-- The variance of a circle average: `Var(h_r(z)) = 2 A_r(z) - log r`, `A_r(z)` the average of `logMaxAbs` on `∂B_r(z)`. -/
theorem wholePlaneGFFCov_circle_self_eq {r : ℝ} (hr : 0 < r) (z : ℂ) :
    wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle r z) =
      2 * Real.circleAverage logMaxAbs z r - Real.log r := by
  rw [wholePlaneGFFCov_circle_circle_eq (r := r) (s := r) hr z z]
  have hEq : Set.EqOn (fun x : ℂ => Real.log (max r ‖x - z‖)) (fun _ : ℂ => Real.log r) (sphere z |r|) := by
    intro x hx
    have hx' : ‖x - z‖ = r := by
      have h := (mem_sphere_iff_norm).1 hx
      rwa [abs_of_pos hr] at h
    show Real.log (max r ‖x - z‖) = Real.log r
    rw [hx', max_self]
  rw [Real.circleAverage_congr_sphere hEq, Real.circleAverage_const]
  ring

/-- Variance of a difference of two circle averages (MQ-lh-17 (b), B4): for `a ≤ r`, `a ≤ s`,
`Var(h_r(z) - h_s(w)) ≤ 2 log(max r s + |z - w|) - log r - log s ≤ (|r - s| + 2 |z - w|) / a`. The covariance of the
difference is `K_rr + K_ss - 2 K_rs`; the averages `A_r(z)`, `A_s(w)` cancel, and the cross term is
`avg_{x ∈ ∂B_r(z)} log max(s, |x - w|) ≤ log (max r s + |z - w|)` since `|x - w| ≤ r + |z - w|` on `∂B_r(z)`. -/
theorem wholePlaneGFFCov_circle_increment_le {a r s : ℝ} (ha : 0 < a) (har : a ≤ r) (has : a ≤ s) (z w : ℂ) :
    wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle r z)
      + wholePlaneGFFCov (GFFObservable.circle s w) (GFFObservable.circle s w)
      - 2 * wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle s w)
      ≤ (|r - s| + 2 * ‖z - w‖) / a := by
  have hr : 0 < r := lt_of_lt_of_le ha har
  have hs : 0 < s := lt_of_lt_of_le ha has
  rw [wholePlaneGFFCov_circle_self_eq hr z, wholePlaneGFFCov_circle_self_eq hs w,
    wholePlaneGFFCov_circle_circle_eq (r := r) hs z w]
  have hcLog : Continuous (fun x : ℂ => Real.log (max s ‖x - w‖)) :=
    (continuous_const.max (continuous_id.sub continuous_const).norm).log
      (fun x => (lt_of_lt_of_le hs (le_max_left _ _)).ne')
  have hML : Real.circleAverage (fun x : ℂ => Real.log (max s ‖x - w‖)) z r
      ≤ Real.log (max r s + ‖z - w‖) := by
    have hmono := Real.circleAverage_mono (circleIntegrable_of_continuous hcLog z r)
      (circleIntegrable_of_continuous continuous_const z r)
      (f₂ := fun _ : ℂ => Real.log (max r s + ‖z - w‖))
      (fun x hx => by
        have hx' : ‖x - z‖ = r := by
          have h := (mem_sphere_iff_norm).1 hx
          rwa [abs_of_pos hr] at h
        have h1 : ‖x - w‖ ≤ r + ‖z - w‖ := by
          have e : x - w = (x - z) + (z - w) := by ring
          rw [e]
          exact (norm_add_le _ _).trans (by rw [hx'])
        have h2 : max s ‖x - w‖ ≤ max r s + ‖z - w‖ :=
          max_le (by linarith [le_max_right r s, norm_nonneg (z - w)])
            (by linarith [le_max_left r s])
        exact Real.log_le_log (lt_of_lt_of_le hs (le_max_left _ _)) h2)
    rw [Real.circleAverage_const] at hmono
    exact hmono
  have key := LatticeProb.Gauss.two_log_max_add_sub_log_le ha har has (norm_nonneg (z - w))
  linarith

end HarmonicBalls
