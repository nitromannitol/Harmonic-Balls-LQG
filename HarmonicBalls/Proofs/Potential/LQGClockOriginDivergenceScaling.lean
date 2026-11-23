import HarmonicBalls.Proofs.Potential.LQGClockOneStartSubcritical

/-! # Divergence of the LQG clock from the origin by scaling of the dyadic lower limits

Bertacco and Gwynne (arXiv:2501.15936v2), proof of Theorem 5.12 (B4), for the LQG clock `F` of the
inserted field `h = h^ℂ - α log |·|` (`0 < γ`, `α < Q`) of planar Brownian motion from the origin,
with the clocks of the rescaled fields replaced by raw functionals of the field and the path, so
that no clock other than `F` is constructed.

For `m ≥ 0` let `h^{(m)}` be the field rescaled by `2^m` (again a whole-plane GFF) and
`b̃_m(u) = 2^{-m} b(4^m u)` the rescaled path (again a planar Brownian motion from `0`). The dyadic
lower limits `Y_m = G_{0,1}(h^{(m)}, b̃_m)` of the approximants over `[0, 1]` are read off the
dyadic circle averages of `h^{(m)}` and the path through a measurable functional
(`profileIncrementLiminf`), so they are identically distributed under the joint law of the field
and the path. Brownian scaling of the approximants (`lqgClockApprox_fieldCircleAverage_dyadic_mul_time`)
shifts the dyadic index by `m`, which does not change a lower limit, so
`c_m Y_m = G_{0,4^m}(h, b) ≤ F(4^m)` with `c_m = 2^{m (2 + γ²/2 - γ α)} e^{γ h^ℂ_{2^m}(0)} → ∞`.
If `G_{0,1} > 0` almost surely, the clock is unbounded along the times `4^m`
(`ae_forall_exists_le_of_le_mul_of_map_eq`), and being nondecreasing it tends to infinity.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The dyadic approximant over `[0, t]` is the approximating clock at time `t`. -/
theorem dyadicIncrementApprox_zero_eq (γ : ℝ) (hε : ℝ → ℂ → ℝ) (k : ℕ) (t : ℝ≥0)
    (w : ContinuousPath ℂ) :
    dyadicIncrementApprox γ hε k 0 t w = lqgClockApprox γ hε (dyadicScale k) w t :=
  rfl

/-- Brownian scaling of the dyadic lower limits from time `0`: `G_{0,1}` of the field rescaled by
`2^m` along the rescaled path is `c_m⁻¹ G_{0,4^m}` of the field along the path. -/
theorem dyadicIncrementLiminf_rescaled_eq (hcirc : ℝ → ℂ → ℝ) (α γ : ℝ) (m : ℕ)
    (b : ContinuousPath ℂ) :
    dyadicIncrementLiminf γ
        (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m))) 0 1
        (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b) =
      ENNReal.ofReal ((((2 : ℝ) ^ m) ^ (2 + γ ^ 2 / 2 - γ * α) *
          rexp (γ * hcirc ((2 : ℝ) ^ m) 0))⁻¹) *
        dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α hcirc) 0
          (((((2 : ℝ) ^ m) ^ 2).toNNReal * 1 : ℝ≥0) : ℝ) b := by
  set K := ((2 : ℝ) ^ m) ^ (2 + γ ^ 2 / 2 - γ * α) * rexp (γ * hcirc ((2 : ℝ) ^ m) 0) with hK
  have hK0 : 0 < K := by positivity
  unfold dyadicIncrementLiminf
  rw [← ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top,
    ← Filter.liminf_nat_add (fun k => ENNReal.ofReal (dyadicIncrementApprox γ
      (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m))) k 0 1
      (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b))) m]
  congr 1
  funext k
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hK0.le)]
  congr 1
  have h1 : dyadicIncrementApprox γ
      (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m))) (k + m)
        0 1 (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b) =
      lqgClockApprox γ
        (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m)))
        (dyadicScale (k + m)) (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b)
        1 := by
    simpa using dyadicIncrementApprox_zero_eq γ
      (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage hcirc ((2 : ℝ) ^ m))) (k + m)
      1 (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b)
  rw [h1, dyadicIncrementApprox_zero_eq, lqgClockApprox_fieldCircleAverage_dyadic_mul_time hcirc α
    γ m k b 1, ← hK, ← mul_assoc, inv_mul_cancel₀ hK0.ne', one_mul]

/-- **Divergence of the clock from the origin** (Bertacco-Gwynne 2025, Theorem 5.12 (B4)): if for
almost every field the lower limit `G_{0,1}` of the dyadic approximants over `[0, 1]` is almost
surely positive from the origin, then for almost every field the LQG clock from the origin almost
surely tends to infinity. -/
theorem ae_ae_tendsto_atTop_lqgClock_origin_of_dyadicIncrementLiminf_pos {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hα : α < lqgQ γ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (F ω))
    (hpos : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion 0),
      0 < dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 1 b) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion 0), Tendsto (F ω b) atTop atTop := by
  have hP := hh.isProbabilityMeasure
  set Q := planarBrownianMotion (0 : ℂ) with hQdef
  let cm : ℕ → ℝ≥0 := fun m => (((2 : ℝ) ^ m) ^ 2).toNNReal
  have hcm (m : ℕ) : 0 < cm m := by
    simp only [cm, Real.toNNReal_pos]
    positivity
  let S : ℕ → ContinuousPath ℂ → ContinuousPath ℂ := fun m =>
    Section6.scaledCenteredPlanarPath 0 (cm m)
  have hSm (m : ℕ) : Measurable (S m) :=
    (Section6.continuous_scaledCenteredPlanarPath 0 (cm m)).measurable
  have hSmap (m : ℕ) : Q.map (S m) = Q :=
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
  -- the raw dyadic profiles of the rescaled fields and their laws
  let O : ℕ → Ω → ℕ × ℂ → ℝ := fun m ω p => hc' m ω (dyadicScale p.1) p.2
  have hOm (m : ℕ) : Measurable (O m) := measurable_dyadicProfile (hh'' m)
  have hHB (m : ℕ) : HarmonicBalls.IsWholePlaneGFF P _ (hc' m) :=
    (LPBridge.isWholePlaneGFF_iff P _ _).mpr (hh'' m)
  let Ψ : (GFFObservable.Admissible → ℝ) → ℕ × ℂ → ℝ := fun f p =>
    f ⟨.circle (dyadicScale p.1) p.2, dyadicScale_pos p.1⟩
  have hΨ : Measurable Ψ := measurable_pi_iff.mpr fun p => measurable_pi_apply _
  have hOlaw (m : ℕ) : P.map (O m) = P.map (O 0) :=
    (((hHB m).identDistrib_observables (hHB 0)).comp hΨ).map_eq
  have hpair (m : ℕ) : IdentDistrib (fun p : Ω × ContinuousPath ℂ => (O m p.1, S m p.2))
      (fun p : Ω × ContinuousPath ℂ => (O 0 p.1, S 0 p.2)) (P.prod Q) (P.prod Q) := by
    refine ⟨((hOm m).comp measurable_fst |>.prodMk ((hSm m).comp measurable_snd)).aemeasurable,
      ((hOm 0).comp measurable_fst |>.prodMk ((hSm 0).comp measurable_snd)).aemeasurable, ?_⟩
    have h1 := Measure.map_prod_map P Q (hOm m) (hSm m)
    have h2 := Measure.map_prod_map P Q (hOm 0) (hSm 0)
    rw [hSmap m] at h1
    rw [hSmap 0, ← hOlaw m] at h2
    exact h1.symm.trans h2
  -- the lower limits over `[0, 1]` along the rescaled fields and paths
  let Φ : (ℕ × ℂ → ℝ) × ContinuousPath ℂ → ℝ := fun q =>
    (profileIncrementLiminf γ α 0 1 q.1 q.2).toReal
  have hΦ : Measurable Φ :=
    (measurable_profileIncrementLiminf_comp γ α 0 1 measurable_fst measurable_snd).ennreal_toReal
  let Y : ℕ → Ω × ContinuousPath ℂ → ℝ := fun m p => Φ (O m p.1, S m p.2)
  have hYm (m : ℕ) : Measurable (Y m) :=
    hΦ.comp (((hOm m).comp measurable_fst).prodMk ((hSm m).comp measurable_snd))
  have hlaw (m : ℕ) : (P.prod Q).map (Y m) = (P.prod Q).map (Y 0) :=
    ((hpair m).comp hΦ).map_eq
  -- continuity of the circle averages
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hh.ae_continuousOn_circle] with ω hω r hr
    exact hω.comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hr, mem_univ _⟩
  have hcont' : ∀ ω, (∀ r, 0 < r → Continuous (hcirc ω r)) → ∀ m k,
      Continuous (hc' m ω (dyadicScale k)) := by
    intro ω hω m k
    have hn : 0 < ‖(((2 : ℝ) ^ m : ℝ) : ℂ)‖ := norm_pos_iff.mpr (ha m)
    exact ((hω _ (mul_pos hn (dyadicScale_pos k))).comp
      ((continuous_const.mul continuous_id).add continuous_const)).sub continuous_const
  have hcontF : ∀ ω, (∀ r, 0 < r → Continuous (hcirc ω r)) → ∀ k,
      Continuous (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k)) := by
    intro ω hω k
    have h : LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) =
        fun z => hcirc ω (dyadicScale k) z - α * Real.log (max (dyadicScale k) ‖z‖) :=
      funext (fieldCircleAverage_dyadic_eq α (hcirc ω) k)
    rw [h]
    exact (hω _ (dyadicScale_pos k)).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log fun z =>
        ne_of_gt (lt_of_lt_of_le (dyadicScale_pos k) (le_max_left _ _))))
  have hYeq : ∀ ω, (∀ r, 0 < r → Continuous (hcirc ω r)) → ∀ m b, Y m (ω, b) =
      (dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α (hc' m ω)) 0 1
        (S m b)).toReal := by
    intro ω hω m b
    show (profileIncrementLiminf γ α 0 1 (fun p => hc' m ω (dyadicScale p.1) p.2)
      (S m b)).toReal = _
    rw [profileIncrementLiminf_eq_dyadicIncrementLiminf zero_le_one (hcont' ω hω m) (S m b)]
  -- the scaling inequality `c_m Y_m ≤ F(4^m)`
  let c : ℕ → Ω × ContinuousPath ℂ → ℝ := fun m p =>
    ((2 : ℝ) ^ m) ^ (2 + γ ^ 2 / 2 - γ * α) * Real.exp (γ * hcirc p.1 ((2 : ℝ) ^ m) 0)
  have hcpos (m : ℕ) (p : Ω × ContinuousPath ℂ) : 0 < c m p := by positivity
  have hscale : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, ∀ m, c m (ω, b) * Y m (ω, b) ≤ F ω b (cm m * 1) := by
    filter_upwards [hF, hcont] with ω hω hcω
    rw [ae_all_iff]
    intro m
    have hsa : (((0 : ℝ≥0) : ℝ)) ≤ 0 := by simp
    have hbt : ((cm m * 1 : ℝ≥0) : ℝ) ≤ ((cm m * 1 : ℝ≥0) : ℝ) := le_rfl
    filter_upwards [ae_dyadicIncrementLiminf_le_of_isLQGClock hω (hcontF ω hcω) hsa
      (NNReal.coe_nonneg _) hbt, ae_zero_continuous_monotone_of_isLQGClock (hcontF ω hcω) hω]
      with b hb hb0
    rw [hb0.1, sub_zero] at hb
    have hG := dyadicIncrementLiminf_rescaled_eq (hcirc ω) α γ m b
    rw [hYeq ω hcω m b]
    show c m (ω, b) * (dyadicIncrementLiminf γ (LatticeProb.Gauss.fieldCircleAverage α
      (rescaledCircleAverage (hcirc ω) ((2 : ℝ) ^ m))) 0 1
        (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal b)).toReal ≤ _
    rw [hG]
    have hFnn : 0 ≤ F ω b (cm m * 1) := by
      have := hb0.2.2 (show (0 : ℝ≥0) ≤ cm m * 1 from zero_le)
      rwa [hb0.1] at this
    have hle : (ENNReal.ofReal ((c m (ω, b))⁻¹) * dyadicIncrementLiminf γ
        (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 ((cm m * 1 : ℝ≥0) : ℝ) b).toReal ≤
        (c m (ω, b))⁻¹ * F ω b (cm m * 1) := by
      have h2 : ENNReal.ofReal ((c m (ω, b))⁻¹) * dyadicIncrementLiminf γ
          (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 ((cm m * 1 : ℝ≥0) : ℝ) b ≤
          ENNReal.ofReal ((c m (ω, b))⁻¹) * ENNReal.ofReal (F ω b (cm m * 1)) := by
        gcongr
      refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
        h2).trans_eq ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (hcpos m _).le),
        ENNReal.toReal_ofReal hFnn]
    calc c m (ω, b) * (ENNReal.ofReal ((c m (ω, b))⁻¹) * dyadicIncrementLiminf γ
          (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 ((cm m * 1 : ℝ≥0) : ℝ) b).toReal
        ≤ c m (ω, b) * ((c m (ω, b))⁻¹ * F ω b (cm m * 1)) :=
          mul_le_mul_of_nonneg_left hle (hcpos m _).le
      _ = F ω b (cm m * 1) := by rw [← mul_assoc, mul_inv_cancel₀ (hcpos m _).ne', one_mul]
  -- the prefactors diverge
  have ha0 : 0 < 2 + γ ^ 2 / 2 - γ * α := by
    have hQ : γ * lqgQ γ = 2 + γ ^ 2 / 2 := by
      rw [lqgQ]
      field_simp
    have : 0 < γ * (lqgQ γ - α) := mul_pos hγ (by linarith)
    nlinarith
  have hc : ∀ᵐ p ∂(P.prod Q), Tendsto (fun m => c m p) atTop atTop := by
    have h := Measure.QuasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := Q))
      (ae_tendsto_rpow_mul_exp_circle_atTop hh γ ha0)
    filter_upwards [h] with p hp
    exact hp
  -- positivity of `Y_0`
  have hpos0 : ∀ᵐ p ∂(P.prod Q), 0 < Y 0 p := by
    refine (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_const (hYm 0))).mpr ?_
    filter_upwards [hF, hpos, hh.ae_circleAverage_one_zero, hcont] with ω hω hpω h1ω hcω
    have hsa : (((0 : ℝ≥0) : ℝ)) ≤ 0 := by simp
    have hbt : (1 : ℝ) ≤ ((1 : ℝ≥0) : ℝ) := by simp
    filter_upwards [hpω, ae_dyadicIncrementLiminf_le_of_isLQGClock hω (hcontF ω hcω) hsa
      zero_le_one hbt] with b hb hle
    have hfield : LatticeProb.Gauss.fieldCircleAverage α (hc' 0 ω) =
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) := by
      funext r z
      simp [hc', rescaledCircleAverage, LatticeProb.Gauss.fieldCircleAverage, h1ω]
    show 0 < Y 0 (ω, b)
    rw [hYeq ω hcω 0 b, hfield, hS0]
    exact ENNReal.toReal_pos hb.ne' (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  -- conclusion
  have hunb := Measure.ae_ae_of_ae_prod
    (ae_forall_exists_le_of_le_mul_of_map_eq (μ := P.prod Q) (fun m p => c m p * Y m p) c Y
      (fun m => ae_of_all _ fun p => le_rfl) hc hYm hlaw hpos0)
  have hmono : ∀ᵐ ω ∂P, ∀ᵐ b ∂Q, Monotone (F ω b) := by
    filter_upwards [hF, hcont] with ω hω hcω
    filter_upwards [ae_zero_continuous_monotone_of_isLQGClock (hcontF ω hcω) hω] with b hb
    exact hb.2.2
  filter_upwards [hunb, hscale, hmono] with ω h1 h2 h3
  filter_upwards [h1, h2, h3] with b hb1 hb2 hb3
  refine tendsto_atTop_atTop_of_monotone hb3 fun M => ?_
  obtain ⟨m, hm⟩ := hb1 M
  exact ⟨cm m * 1, hm.trans (hb2 m)⟩

end HarmonicBalls
