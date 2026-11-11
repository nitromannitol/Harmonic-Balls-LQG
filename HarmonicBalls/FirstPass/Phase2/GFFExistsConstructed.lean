import HarmonicBalls.FirstPass.S11u.Kernel
import HarmonicBalls.LPStage.GFFExistence
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.Phase2.GFFExistsDerived
import HarmonicBalls.LPStage.GFFCovSymm

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

/-! ### Row 29: `WholePlaneGFFExistsFrozen` from the LP construction

Conditional on the two named inputs of `HarmonicBalls/LPStage/GFFExistence.lean`: `WholePlaneCovPSDStmt` (B2, positive
semidefiniteness of the covariance, MQ-lh-25) and `WholePlaneCovSymmStmt` (symmetry of the covariance). The Kolmogorov
extension (B1) is proved (`LatticeProb.exists_isProjectiveLimit_real`). The kernel increment bound is discharged here from
`wholePlaneGFFCov_circle_increment_le`. -/

/-- The circle observable of a parameter point, as an LP observable. -/
lemma ptObs_eq_circle {p : ℝ × (Fin 2 → ℝ)} (hp : 0 < p.1) :
    LatticeProb.Gauss.ptObs p = LatticeProb.Gauss.GFFObservable.circle p.1 (LatticeProb.Gauss.cplxOf p.2) := by
  simp [LatticeProb.Gauss.ptObs, hp]

/-- `‖cplxOf v - cplxOf u‖ ≤ 2 dist (r, v) (s, u)` for the centre components in the sup norm. -/
lemma norm_cplxOf_sub_le (p q : ℝ × (Fin 2 → ℝ)) :
    ‖LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2‖ ≤ 2 * dist p q := by
  have hd0 : dist (p.2 0) (q.2 0) ≤ dist p q :=
    (dist_le_pi_dist p.2 q.2 0).trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  have hd1 : dist (p.2 1) (q.2 1) ≤ dist p q :=
    (dist_le_pi_dist p.2 q.2 1).trans (by rw [Prod.dist_eq]; exact le_max_right _ _)
  rw [Real.dist_eq] at hd0 hd1
  have hre : |(LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2).re| ≤ dist p q := by
    simpa [LatticeProb.Gauss.cplxOf] using hd0
  have him : |(LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2).im| ≤ dist p q := by
    simpa [LatticeProb.Gauss.cplxOf] using hd1
  calc ‖LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2‖
      ≤ |(LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2).re|
        + |(LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * dist p q := by linarith

/-- The kernel increment bound of the LP kernel on circle parameters (the hypothesis `hvarK` of
`LatticeProb.Gauss.exists_isWholePlaneGFF`), from `wholePlaneGFFCov_circle_increment_le`. -/
theorem lp_increment_bound :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, 0 ≤ C ∧ ∀ p q : ℝ × (Fin 2 → ℝ), a ≤ p.1 → a ≤ q.1 →
      LatticeProb.Gauss.wholePlaneGFFCov (LatticeProb.Gauss.ptObs p) (LatticeProb.Gauss.ptObs p)
        + LatticeProb.Gauss.wholePlaneGFFCov (LatticeProb.Gauss.ptObs q) (LatticeProb.Gauss.ptObs q)
        - 2 * LatticeProb.Gauss.wholePlaneGFFCov (LatticeProb.Gauss.ptObs p) (LatticeProb.Gauss.ptObs q)
        ≤ C * dist p q := by
  intro a ha
  refine ⟨5 / a, by positivity, fun p q hp hq => ?_⟩
  have hp0 : 0 < p.1 := lt_of_lt_of_le ha hp
  have hq0 : 0 < q.1 := lt_of_lt_of_le ha hq
  rw [ptObs_eq_circle hp0, ptObs_eq_circle hq0]
  have hK : ∀ (r s : ℝ) (z w : ℂ),
      LatticeProb.Gauss.wholePlaneGFFCov (LatticeProb.Gauss.GFFObservable.circle r z)
          (LatticeProb.Gauss.GFFObservable.circle s w)
        = wholePlaneGFFCov (GFFObservable.circle r z) (GFFObservable.circle s w) :=
    fun _ _ _ _ => rfl
  rw [hK, hK, hK]
  have h := wholePlaneGFFCov_circle_increment_le ha hp hq (LatticeProb.Gauss.cplxOf p.2)
    (LatticeProb.Gauss.cplxOf q.2)
  refine h.trans ?_
  have h1 : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, ← Real.dist_eq]
    exact le_max_left _ _
  have h2 := norm_cplxOf_sub_le p q
  have hsum : |p.1 - q.1| + 2 * ‖LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2‖
      ≤ 5 * dist p q := by linarith
  calc (|p.1 - q.1| + 2 * ‖LatticeProb.Gauss.cplxOf p.2 - LatticeProb.Gauss.cplxOf q.2‖) / a
      ≤ (5 * dist p q) / a := div_le_div_of_nonneg_right hsum ha.le
    _ = 5 / a * dist p q := by ring

/-- Row 29, universe `0`: a whole-plane GFF exists (`WholePlaneGFFExistsFrozen.{0}`), conditional on the named inputs
`WholePlaneCovPSDStmt` (B2) and `WholePlaneCovSymmStmt`. -/
theorem wholePlaneGFFExistsFrozen_zero_derived (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt)
    (hsymm : LatticeProb.Gauss.WholePlaneCovSymmStmt) : WholePlaneGFFExistsFrozen.{0} := by
  obtain ⟨Ω, mΩ, P, hP, hC, hcirc, h⟩ :=
    LatticeProb.Gauss.exists_isWholePlaneGFF hB2 hsymm lp_increment_bound
  exact ⟨Ω, mΩ, P, hP, hC, hcirc, (HarmonicBalls.LPBridge.isWholePlaneGFF_iff P hC hcirc).mpr h⟩

universe u

/-- Row 29, every universe `u`, conditional on the same named inputs (`ULift` of the universe-`0` statement). -/
theorem wholePlaneGFFExistsFrozen_derived (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt)
    (hsymm : LatticeProb.Gauss.WholePlaneCovSymmStmt) : WholePlaneGFFExistsFrozen.{u} :=
  wholePlaneGFFExists_ulift (wholePlaneGFFExistsFrozen_zero_derived hB2 hsymm)


/-- Row 29, universe `0`, with the symmetry input discharged by `LatticeProb.Gauss.wholePlaneCovSymm_proved`
(`LPStage/GFFCovSymm.lean`): conditional on the single named input `WholePlaneCovPSDStmt` (B2). The earlier
`wholePlaneGFFExistsFrozen_zero_derived` (with the named symmetry input) is kept. -/
theorem wholePlaneGFFExistsFrozen_zero_derived_of_psd (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt) :
    WholePlaneGFFExistsFrozen.{0} := by
  obtain ⟨Ω, mΩ, P, hP, hC, hcirc, h⟩ :=
    LatticeProb.Gauss.exists_isWholePlaneGFF_of_psd hB2 lp_increment_bound
  exact ⟨Ω, mΩ, P, hP, hC, hcirc, (HarmonicBalls.LPBridge.isWholePlaneGFF_iff P hC hcirc).mpr h⟩

/-- Row 29, every universe `u`, conditional on `WholePlaneCovPSDStmt` only (`ULift` of the universe-`0` statement). -/
theorem wholePlaneGFFExistsFrozen_derived_of_psd (hB2 : LatticeProb.Gauss.WholePlaneCovPSDStmt) :
    WholePlaneGFFExistsFrozen.{u} :=
  wholePlaneGFFExists_ulift (wholePlaneGFFExistsFrozen_zero_derived_of_psd hB2)

end HarmonicBalls
