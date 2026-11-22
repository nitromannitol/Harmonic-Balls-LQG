import HarmonicBalls.Proofs.Potential.LQGClockOriginDivergence
import HarmonicBalls.Proofs.Potential.LQGClockMeasurableVersion
import HarmonicBalls.Proofs.Potential.LQGClockApproxPathDecoder
import HarmonicBalls.Proofs.Sec5.GaussianProcessLaw
import LatticeProb.Gauss.GFFAffineInvariance

/-! # Divergence of the LQG clock from the origin from its positivity

Bertacco and Gwynne (arXiv:2501.15936v2), proof of Theorem 5.12 (B4), for the LQG clock of the
inserted field `h = h^ℂ - α log |·|` (`0 < γ`, `γ² < 2`, `α < Q`) of planar Brownian motion from
the origin: if for almost every field the clock is almost surely positive at time `1`, then for
almost every field it almost surely tends to infinity.

For `m ≥ 0` the field rescaled by `2^m` is again a whole-plane GFF (affine invariance), so it has
an LQG clock `F'_m` from the origin; the approximating clocks of all these fields along the
rescaled paths `b̃_m(u) = 2^{-m} b(4^m u)` are measurable functions of the circle averages and of
the path (`exists_measurable_lqgClockApprox_decoder`), and since the circle averages of the
rescaled fields have the law of those of the field and `b̃_m` is again a planar Brownian motion
from the origin, the sequences of approximations at time `1` are identically distributed under
the joint law of the field and the path. Their limits in probability `Y_m = F'_m(b̃_m)(1)` (taken
jointly measurable, `exists_measurable_tendstoInMeasure_prod`) are therefore identically
distributed (`identDistrib_of_tendstoInMeasure`). With the scaling identity
`F(4^m) = c_m Y_m` (`ae_lqgClock_mul_time_eq`), the divergence of the prefactors `c_m`
(`ae_tendsto_rpow_mul_exp_circle_atTop`) and the positivity of `Y_0`, which is the clock at time
`1` since the unit circle average vanishes, the clock is unbounded along the times `4^m`
(`ae_forall_exists_le_of_le_mul_of_map_eq`), and being nondecreasing it tends to infinity.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The deduction of `ae_tendsto_atTop_of_le_mul_of_map_eq` along a sequence: if `c n * Y n ≤ Z n`
almost surely, `c n → ∞` almost surely and the `Y n` are identically distributed and almost
surely positive, then almost surely the sequence `Z n` is unbounded above. -/
theorem ae_forall_exists_le_of_le_mul_of_map_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (Z c Y : ℕ → X → ℝ) (hscale : ∀ n, ∀ᵐ p ∂μ, c n p * Y n p ≤ Z n p)
    (hc : ∀ᵐ p ∂μ, Tendsto (fun n => c n p) atTop atTop)
    (hYm : ∀ n, Measurable (Y n)) (hlaw : ∀ n, μ.map (Y n) = μ.map (Y 0))
    (hpos : ∀ᵐ p ∂μ, 0 < Y 0 p) :
    ∀ᵐ p ∂μ, ∀ M : ℝ, ∃ n, M ≤ Z n p := by
  let F : X → ℝ≥0 → ℝ := fun p t =>
    (Finset.range (⌊t⌋₊ + 1)).sup' Finset.nonempty_range_add_one fun n => Z n p
  have hFmono (p : X) : Monotone (F p) := by
    intro s t hst
    have hsub : Finset.range (⌊s⌋₊ + 1) ⊆ Finset.range (⌊t⌋₊ + 1) :=
      Finset.range_subset_range.mpr (Nat.add_le_add_right (Nat.floor_mono hst) 1)
    exact Finset.sup'_le _ _ fun n hn => Finset.le_sup' (fun n => Z n p) (hsub hn)
  have hFZ (n : ℕ) (p : X) : Z n p ≤ F p (n : ℝ≥0) :=
    Finset.le_sup' (fun n => Z n p) (by simp)
  have hscale' : ∀ n, ∀ᵐ p ∂μ, c n p * Y n p ≤ F p ((fun (n : ℕ) (_ : X) => (n : ℝ≥0)) n p) := by
    intro n
    filter_upwards [hscale n] with p hp
    exact hp.trans (hFZ n p)
  filter_upwards [ae_monotone_imp_tendsto_atTop_of_le_mul_of_map_eq F
    (fun n _ => (n : ℝ≥0)) c Y hscale' hc hYm hlaw hpos] with p hp M
  obtain ⟨t, ht⟩ := ((hp (hFmono p)).eventually_ge_atTop M).exists
  obtain ⟨n, -, hn⟩ := (Finset.le_sup'_iff _).mp ht
  exact ⟨n, hn⟩

/-- Quenched convergence in probability at a fixed time along a measure-preserving map of
paths: if `F` is an LQG clock and `D k` agrees with the approximating clocks at time `t` along
`S b`, then `D k` converges in probability to `F (S b) t`. -/
theorem tendstoInMeasure_of_isLQGClock_comp {γ : ℝ} {hε : ℝ → ℂ → ℝ} {x : ℂ}
    {F : ContinuousPath ℂ → ℝ≥0 → ℝ} (hF : IsLQGClock planarBrownianMotion γ hε x F)
    {S : ContinuousPath ℂ → ContinuousPath ℂ} (hSm : Measurable S)
    (hSmap : (planarBrownianMotion x).map S = planarBrownianMotion x) (t : ℝ≥0)
    {D : ℕ → ContinuousPath ℂ → ℝ}
    (hD : ∀ k b, D k b = lqgClockApprox γ hε (dyadicScale k) (S b) t) :
    TendstoInMeasure (planarBrownianMotion x) D atTop (fun b => F (S b) t) := by
  rw [tendstoInMeasure_iff_norm]
  intro η hη
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hF t η hη)
    (fun k => zero_le) fun k => ?_
  refine le_trans (measure_mono ?_) ((Measure.le_map_apply hSm.aemeasurable _).trans_eq
    (by rw [hSmap]))
  intro b hb
  simp only [mem_ofPred_eq, Real.norm_eq_abs, hD] at hb
  exact ⟨t, le_rfl, hb⟩

/-- Bertacco-Gwynne 2025, Theorem 5.12 (B4), for the LQG clock of the inserted field from the
origin: if for almost every field the clock is almost surely positive at time `1`, then for
almost every field it almost surely tends to infinity. -/
theorem ae_ae_tendsto_atTop_lqgClock_origin_of_pos {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (F ω))
    (hpos : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion 0), 0 < F ω b 1) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion 0), Tendsto (F ω b) atTop atTop := by
  have hP := hh.isProbabilityMeasure
  let cm : ℕ → ℝ≥0 := fun m => (((2 : ℝ) ^ m) ^ 2).toNNReal
  have hcm (m : ℕ) : 0 < cm m := by
    simp only [cm, Real.toNNReal_pos]
    positivity
  let S : ℕ → ContinuousPath ℂ → ContinuousPath ℂ := fun m =>
    Section6.scaledCenteredPlanarPath 0 (cm m)
  have hSm (m : ℕ) : Measurable (S m) :=
    (Section6.continuous_scaledCenteredPlanarPath 0 (cm m)).measurable
  have hSmap (m : ℕ) : (planarBrownianMotion (0 : ℂ)).map (S m) = (planarBrownianMotion (0 : ℂ)) :=
    Section6.planarBrownianMotion_map_scaledCenteredPlanarPath 0 (hcm m).ne'
  have hS0 (b : ContinuousPath ℂ) : S 0 b = b := by
    ext t
    simp [S, cm, Section6.scaledCenteredPlanarPath]
  let hc' : ℕ → Ω → ℝ → ℂ → ℝ := fun m ω => rescaledCircleAverage (hcirc ω) ((2 : ℝ) ^ m)
  have ha (m : ℕ) : (((2 : ℝ) ^ m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (pow_pos (by norm_num : (0 : ℝ) < 2) m).ne'
  have hh' (m : ℕ) := LatticeProb.LQG.AffineDerived.wholePlaneGFFAffineInvariance_lp P hC hcirc hh
    (((2 : ℝ) ^ m : ℝ) : ℂ) (ha m) 0
  have hh'' (m : ℕ) : LatticeProb.Gauss.IsWholePlaneGFF P _ (hc' m) := hh' m
  choose F' hF' using fun m => exists_ae_isLQGClock_fieldCircleAverage (hh'' m) 0 hγ hγ2 hα
  choose D hDm hDeq using fun (k : ℕ) (t : ℝ≥0) =>
    exists_measurable_lqgClockApprox_decoder γ (dyadicScale_pos k).le t
  let O : ℕ → Ω → ℕ → ℂ → ℝ := fun m ω k =>
    LatticeProb.Gauss.fieldCircleAverage α (hc' m ω) (dyadicScale k)
  let O₀ : Ω → ℕ → ℂ → ℝ := fun ω k =>
    LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k)
  have hOm (m : ℕ) : Measurable (O m) := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun z => ?_
    simp only [O, LatticeProb.Gauss.fieldCircleAverage]
    exact ((hh'' m).measurable_circle _ z (dyadicScale_pos k)).sub measurable_const
  have hO₀m : Measurable O₀ := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun z => ?_
    simp only [O₀, LatticeProb.Gauss.fieldCircleAverage]
    exact (hh.measurable_circle _ z (dyadicScale_pos k)).sub measurable_const
  have hOc (m : ℕ) : ∀ᵐ ω ∂P, ∀ k, Continuous (O m ω k) := by
    filter_upwards [ae_continuous_fieldCircleAverage (hh'' m) α] with ω hω k
    exact hω _ (dyadicScale_pos k)
  have hO₀c : ∀ᵐ ω ∂P, ∀ k, Continuous (O₀ ω k) := by
    filter_upwards [ae_continuous_fieldCircleAverage hh α] with ω hω k
    exact hω _ (dyadicScale_pos k)
  let A : ℕ → ℕ → Ω × ContinuousPath ℂ → ℝ := fun m k p => D k 1 (O m p.1 k, S m p.2)
  let A₀ : ℕ → ℕ → Ω × ContinuousPath ℂ → ℝ := fun m k p => D k (cm m * 1) (O₀ p.1 k, p.2)
  have hAm (m k : ℕ) : Measurable (A m k) :=
    (hDm k 1).comp (((measurable_pi_apply k).comp ((hOm m).comp measurable_fst)).prodMk
      ((hSm m).comp measurable_snd))
  have hA₀m (m k : ℕ) : Measurable (A₀ m k) :=
    (hDm k (cm m * 1)).comp (((measurable_pi_apply k).comp (hO₀m.comp measurable_fst)).prodMk
      measurable_snd)
  have hYex (m : ℕ) := exists_measurable_tendstoInMeasure_prod (P := P)
    (ν := planarBrownianMotion (0 : ℂ)) (hAm m)
    (F := fun ω b => F' m ω (S m b) 1) (by
      filter_upwards [hF' m, hOc m] with ω hω hωc
      exact tendstoInMeasure_of_isLQGClock_comp hω (hSm m) (hSmap m) 1
        fun k b => hDeq k 1 _ (hωc k) (S m b))
  choose Y hYm hYlim hYeq using hYex
  have hZex (m : ℕ) := exists_measurable_tendstoInMeasure_prod (P := P)
    (ν := planarBrownianMotion (0 : ℂ)) (hA₀m m)
    (F := fun ω b => F ω b (cm m * 1)) (by
      filter_upwards [hF, hO₀c] with ω hω hωc
      exact tendstoInMeasure_of_isLQGClock_comp (S := id) hω measurable_id (by simp)
        (cm m * 1) fun k b => hDeq k (cm m * 1) _ (hωc k) b)
  choose Z hZm hZlim hZeq using hZex
  have hHB (m : ℕ) : HarmonicBalls.IsWholePlaneGFF P _ (hc' m) :=
    (LPBridge.isWholePlaneGFF_iff P _ _).mpr (hh'' m)
  let Ψ : (GFFObservable.Admissible → ℝ) → ℕ → ℂ → ℝ := fun f k z =>
    f ⟨.circle (dyadicScale k) z, dyadicScale_pos k⟩ -
      α * Real.circleAverage (fun x => Real.log ‖x‖) z (dyadicScale k)
  have hΨ : Measurable Ψ := by
    refine measurable_pi_iff.mpr fun k => measurable_pi_iff.mpr fun z => ?_
    exact (measurable_pi_apply _).sub measurable_const
  have hOlaw (m : ℕ) : P.map (O m) = P.map (O 0) := by
    have h := ((hHB m).identDistrib_observables (hHB 0)).comp hΨ
    exact h.map_eq
  let Φ : (ℕ → ℂ → ℝ) × ContinuousPath ℂ → ℕ → ℝ := fun q k => D k 1 (q.1 k, q.2)
  have hΦ : Measurable Φ :=
    measurable_pi_iff.mpr fun k => (hDm k 1).comp
      (((measurable_pi_apply k).comp measurable_fst).prodMk measurable_snd)
  have hpair (m : ℕ) : IdentDistrib (fun p : Ω × ContinuousPath ℂ => (O m p.1, S m p.2))
      (fun p : Ω × ContinuousPath ℂ => (O 0 p.1, S 0 p.2)) (P.prod (planarBrownianMotion (0 : ℂ)))
      (P.prod (planarBrownianMotion (0 : ℂ))) := by
    refine ⟨((hOm m).comp measurable_fst |>.prodMk ((hSm m).comp measurable_snd)).aemeasurable,
      ((hOm 0).comp measurable_fst |>.prodMk ((hSm 0).comp measurable_snd)).aemeasurable, ?_⟩
    have h1 := Measure.map_prod_map P (planarBrownianMotion (0 : ℂ)) (hOm m) (hSm m)
    have h2 := Measure.map_prod_map P (planarBrownianMotion (0 : ℂ)) (hOm 0) (hSm 0)
    rw [hSmap m] at h1
    rw [hSmap 0, ← hOlaw m] at h2
    exact h1.symm.trans h2
  have hAid (m : ℕ) : IdentDistrib (fun p k => A m k p) (fun p k => A 0 k p)
      (P.prod (planarBrownianMotion (0 : ℂ))) (P.prod (planarBrownianMotion (0 : ℂ))) :=
    (hpair m).comp hΦ
  have hlaw (m : ℕ) :
      (P.prod (planarBrownianMotion (0 : ℂ))).map (Y m) =
        (P.prod (planarBrownianMotion (0 : ℂ))).map (Y 0) :=
    (identDistrib_of_tendstoInMeasure (hAid m) (hYlim m) (hYlim 0)).map_eq
  let c : ℕ → Ω × ContinuousPath ℂ → ℝ := fun m p =>
    ((2 : ℝ) ^ m) ^ (2 + γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc p.1 ((2 : ℝ) ^ m) 0)
  have hcmeas (m : ℕ) : Measurable (c m) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      ((hh.measurable_circle ((2 : ℝ) ^ m) 0 (by positivity)).comp measurable_fst)))
  have hscale (m : ℕ) : ∀ᵐ p ∂(P.prod (planarBrownianMotion (0 : ℂ))), c m p * Y m p ≤ Z m p := by
    have hS : MeasurableSet {p : Ω × ContinuousPath ℂ | c m p * Y m p ≤ Z m p} :=
      measurableSet_le ((hcmeas m).mul (hYm m)) (hZm m)
    refine (Measure.ae_prod_iff_ae_ae hS).mpr ?_
    filter_upwards [hF, hF' m, hYeq m, hZeq m] with ω hω hω' hYω hZω
    filter_upwards [ae_lqgClock_mul_time_eq m hω hω', hYω, hZω] with b hb hYb hZb
    show c m (ω, b) * Y m (ω, b) ≤ Z m (ω, b)
    rw [hYb, hZb]
    exact le_of_eq (hb 1).symm
  have ha0 : 0 < 2 + γ ^ 2 / 2 - γ * α := by
    have hγ0 : γ ≠ 0 := hγ.ne'
    have hQ : γ * lqgQ γ = 2 + γ ^ 2 / 2 := by
      rw [lqgQ]
      field_simp
    have : 0 < γ * (lqgQ γ - α) := mul_pos hγ (by linarith)
    nlinarith
  have hc : ∀ᵐ p ∂(P.prod (planarBrownianMotion (0 : ℂ))),
      Tendsto (fun m => c m p) atTop atTop := by
    have h := Measure.QuasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion (0 : ℂ)))
      (ae_tendsto_rpow_mul_exp_circle_atTop hh γ ha0)
    filter_upwards [h] with p hp
    exact hp
  have hpos0 : ∀ᵐ p ∂(P.prod (planarBrownianMotion (0 : ℂ))), 0 < Y 0 p := by
    refine (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const (hYm 0))).mpr ?_
    filter_upwards [hF, hF' 0, hYeq 0, hpos, hh.ae_circleAverage_one_zero]
      with ω hω hω' hYω hpω h1ω
    have hfield : LatticeProb.Gauss.fieldCircleAverage α (hc' 0 ω) =
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) := by
      funext r z
      simp [hc', rescaledCircleAverage, LatticeProb.Gauss.fieldCircleAverage, h1ω]
    rw [hfield] at hω'
    filter_upwards [ae_eq_of_isLQGClock hω hω', hYω, hpω] with b hb hYb hpb
    show 0 < Y 0 (ω, b)
    rw [hYb, hS0, ← hb]
    exact hpb
  have hunb := Measure.ae_ae_of_ae_prod
    (ae_forall_exists_le_of_le_mul_of_map_eq (μ := P.prod (planarBrownianMotion (0 : ℂ))) Z c Y
      hscale hc hYm hlaw hpos0)
  have hZall : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion (0 : ℂ)),
      ∀ m, Z m (ω, b) = F ω b (cm m * 1) := by
    filter_upwards [ae_all_iff.mpr hZeq] with ω hω
    exact ae_all_iff.mpr hω
  have hmono : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion (0 : ℂ)), Monotone (F ω b) := by
    filter_upwards [hF, hO₀c] with ω hω hωc
    filter_upwards [ae_zero_continuous_monotone_of_isLQGClock hωc hω] with b hb
    exact hb.2.2
  filter_upwards [hunb, hZall, hmono] with ω h1 h2 h3
  filter_upwards [h1, h2, h3] with b hb1 hb2 hb3
  refine tendsto_atTop_atTop_of_monotone hb3 fun M => ?_
  obtain ⟨m, hm⟩ := hb1 M
  exact ⟨cm m * 1, by rw [← hb2 m]; exact hm⟩

/-- For almost every field, the LQG clock of the inserted field from the origin is almost surely a
time-change clock as soon as, for almost every field, it almost surely increases strictly
between any two rational times: divergence follows from the positivity at time `1`
(`ae_ae_tendsto_atTop_lqgClock_origin_of_pos`). -/
theorem ae_ae_isTimeChangeClock_lqgClock_origin {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hγ2 : γ ^ 2 < 2) (hα : α < lqgQ γ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (F ω))
    (hpos : ∀ᵐ ω ∂P, ∀ s t : ℚ, 0 ≤ s → s < t → ∀ᵐ b ∂(planarBrownianMotion (0 : ℂ)),
      F ω b (s : ℝ).toNNReal < F ω b (t : ℝ).toNNReal) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion (0 : ℂ)), IsTimeChangeClock (F ω b) := by
  have hcont := ae_continuous_fieldCircleAverage hh α
  have hpos1 : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion (0 : ℂ)), 0 < F ω b 1 := by
    filter_upwards [hF, hpos, hcont] with ω hω hpω hcω
    filter_upwards [hpω 0 1 le_rfl zero_lt_one,
      ae_zero_continuous_monotone_of_isLQGClock (fun k => hcω _ (dyadicScale_pos k)) hω]
      with b hb hb0
    simp only [Rat.cast_zero, Real.toNNReal_zero, Rat.cast_one, Real.toNNReal_one] at hb
    rw [hb0.1] at hb
    exact hb
  filter_upwards [hF, hpos, hcont,
    ae_ae_tendsto_atTop_lqgClock_origin_of_pos hh hγ hγ2 hα F hF hpos1] with ω hω hpω hcω hdω
  exact ae_isTimeChangeClock_of_isLQGClock (fun k => hcω _ (dyadicScale_pos k)) hω hpω hdω

end HarmonicBalls
