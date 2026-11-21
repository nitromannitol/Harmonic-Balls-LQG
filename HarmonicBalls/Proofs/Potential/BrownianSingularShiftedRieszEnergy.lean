import HarmonicBalls.Proofs.Potential.BrownianSingularPairAllRadius
import HarmonicBalls.Proofs.Potential.BrownianUniformBallOccupation
import HarmonicBalls.Proofs.Potential.GreenPotentialHolder

/-! # Singular Brownian energies with a Riesz kernel

For planar Brownian motion on the unit time interval, the expected energy
`∫∫ |B_s - z|^(-a) |B_s - B_t|^(-k) ds dt` is finite whenever `0 < a < 2` and `0 < k < 2`.
The proof conditions on the earlier of the two times: the two Brownian increments are
independent, and the inverse moments of a Brownian increment are bounded uniformly over shifts.

Since `max(|u|,|v|) ≥ |u-v|/2`, the singularly weighted pair energy
`∫∫ |B_s - z|^(-q) |B_t - z|^(-q) |B_s - B_t|^(-β) ds dt` then has finite expectation
whenever `q + β < 2`, and it bounds every near-diagonal singular pair occupation at
radius `r` by a multiple of `r ^ β`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set Metric
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Inverse-power moments of a Brownian increment are bounded uniformly over shifts. -/
theorem lintegral_map_increment_enorm_sub_rpow_neg_le (x w : ℂ) {s t : ℝ≥0} (hts : t ≠ s)
    {a c : ℝ} (ha : 0 < a) (hac : a < 2 * c) (hc1 : c < 1) :
    (∫⁻ u, (ENNReal.ofReal ‖u - w‖) ^ (-a)
      ∂((planarBrownianMotion x).map (fun b : ContinuousPath ℂ => b t - b s))) ≤
      ENNReal.ofReal (1 + (2 / Real.pi) ^ c * 2 ^ (2 * c) * |(t : ℝ) - (s : ℝ)| ^ (-c) *
        (a / (2 * c - a))) := by
  have hc0 : 0 < c := by linarith
  have hm : Measurable (fun b : ContinuousPath ℂ => b t - b s) :=
    (ContinuousPath.measurable_coordinateProcess _).sub
      (ContinuousPath.measurable_coordinateProcess _)
  let μ : Measure ℂ := (planarBrownianMotion x).map (fun b : ContinuousPath ℂ => b t - b s)
  have hμ1 : μ univ ≤ ENNReal.ofReal 1 := by
    rw [Measure.map_apply hm MeasurableSet.univ]
    simp
  let A : ℝ := (2 / Real.pi) ^ c * 2 ^ (2 * c) * |(t : ℝ) - (s : ℝ)| ^ (-c)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hball : ∀ r : ℝ, 0 < r → μ (closedBall w r) ≤ ENNReal.ofReal (A * r ^ (2 * c)) := by
    intro r hr
    have hsub : closedBall w r ⊆ ball w (2 * r) := by
      intro y hy
      rw [mem_closedBall] at hy
      rw [mem_ball]
      linarith
    have hset : (fun b : ContinuousPath ℂ => b t - b s) ⁻¹' ball w (2 * r) =
        {b : ContinuousPath ℂ | ‖b t - b s - w‖ < 2 * r} := by
      ext b
      simp [mem_ball, dist_eq_norm]
    calc
      μ (closedBall w r) ≤ μ (ball w (2 * r)) := measure_mono hsub
      _ = planarBrownianMotion x {b | ‖b t - b s - w‖ < 2 * r} := by
        rw [Measure.map_apply hm isOpen_ball.measurableSet, hset]
      _ ≤ ENNReal.ofReal ((2 / Real.pi) ^ c * (2 * r) ^ (2 * c) *
          |(t : ℝ) - (s : ℝ)| ^ (-c)) :=
        planarBrownianMotion_increment_smallBall_rpow_le_uniform_center x w hts
          (by linarith) hc0 hc1
      _ = ENNReal.ofReal (A * r ^ (2 * c)) := by
        rw [Real.mul_rpow (by norm_num) hr.le]
        congr 1
        dsimp [A]
        ring
  have hz : μ {w} = 0 :=
    measure_singleton_eq_zero_of_le_rpow (by linarith : (0 : ℝ) < 2 * c) hball
  have hae : ∀ᵐ u ∂μ, u ≠ w := by
    simpa using (measure_eq_zero_iff_ae_notMem.mp hz)
  have heq : (∫⁻ u, (ENNReal.ofReal ‖u - w‖) ^ (-a) ∂μ) =
      ∫⁻ u, ENNReal.ofReal (‖w - u‖ ^ (-a)) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hae] with u hu
    rw [ENNReal.ofReal_rpow_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hu))]
    simp only [norm_sub_rev]
  change (∫⁻ u, (ENNReal.ofReal ‖u - w‖) ^ (-a) ∂μ) ≤ _
  rw [heq]
  simpa only [A] using lintegral_norm_sub_rpow_neg_le ha hac (by norm_num) hA hμ1 hball

/-- For ordered times, a singular weight at a shifted increment and a Riesz kernel at the
next increment have product expectation, by independence of the increments. -/
theorem lintegral_planarBrownianMotion_shifted_increment_pair_le (x w ε : ℂ) {m M : ℝ≥0}
    (hmM : m < M) (hm : m ≠ 0) {a k c e : ℝ} (ha : 0 < a) (hac : a < 2 * c) (hc1 : c < 1)
    (hk : 0 < k) (hke : k < 2 * e) (he1 : e < 1) :
    (∫⁻ b, (ENNReal.ofReal ‖(b m - b 0) + ε * (b M - b m) + w‖) ^ (-a) *
      (ENNReal.ofReal ‖b M - b m‖) ^ (-k) ∂(planarBrownianMotion x)) ≤
      ENNReal.ofReal (1 + (2 / Real.pi) ^ c * 2 ^ (2 * c) * (m : ℝ) ^ (-c) *
        (a / (2 * c - a))) *
      ENNReal.ofReal (1 + (2 / Real.pi) ^ e * 2 ^ (2 * e) * |(M : ℝ) - (m : ℝ)| ^ (-e) *
        (k / (2 * e - k))) := by
  let P : Measure (ContinuousPath ℂ) := planarBrownianMotion x
  let X : ContinuousPath ℂ → ℂ := fun b => b m - b 0
  let Y : ContinuousPath ℂ → ℂ := fun b => b M - b m
  have hX : Measurable X := (ContinuousPath.measurable_coordinateProcess _).sub
    (ContinuousPath.measurable_coordinateProcess _)
  have hY : Measurable Y := (ContinuousPath.measurable_coordinateProcess _).sub
    (ContinuousPath.measurable_coordinateProcess _)
  have hind : IndepFun X Y P :=
    (planarBrownianMotion_hasIndepIncrements x).indepFun_sub_sub (zero_le : (0 : ℝ≥0) ≤ m) hmM.le
  have hlaw : P.map (fun b => (X b, Y b)) = (P.map X).prod (P.map Y) :=
    IndepFun.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable hind
  let g : ℂ × ℂ → ℝ≥0∞ := fun p =>
    (ENNReal.ofReal ‖p.1 + ε * p.2 + w‖) ^ (-a) * (ENNReal.ofReal ‖p.2‖) ^ (-k)
  have hg : Measurable g := by fun_prop
  let K₁ : ℝ≥0∞ := ENNReal.ofReal (1 + (2 / Real.pi) ^ c * 2 ^ (2 * c) * (m : ℝ) ^ (-c) *
    (a / (2 * c - a)))
  let K₂ : ℝ≥0∞ := ENNReal.ofReal (1 + (2 / Real.pi) ^ e * 2 ^ (2 * e) *
    |(M : ℝ) - (m : ℝ)| ^ (-e) * (k / (2 * e - k)))
  have hX1 : ∀ v : ℂ, (∫⁻ u, (ENNReal.ofReal ‖u + ε * v + w‖) ^ (-a) ∂(P.map X)) ≤ K₁ := by
    intro v
    have h := lintegral_map_increment_enorm_sub_rpow_neg_le x (-(ε * v + w)) (s := 0) (t := m)
      hm ha hac hc1
    have h0 : |(m : ℝ) - ((0 : ℝ≥0) : ℝ)| = (m : ℝ) := by simp
    rw [h0] at h
    have hfun : (fun u : ℂ => (ENNReal.ofReal ‖u + ε * v + w‖) ^ (-a)) =
        fun u : ℂ => (ENNReal.ofReal ‖u - -(ε * v + w)‖) ^ (-a) := by
      funext u
      congr 3
      ring
    rw [hfun]
    exact h
  have hY1 : (∫⁻ v, (ENNReal.ofReal ‖v‖) ^ (-k) ∂(P.map Y)) ≤ K₂ := by
    have h := lintegral_map_increment_enorm_sub_rpow_neg_le x 0 (s := m) (t := M)
      hmM.ne' hk hke he1
    simpa only [sub_zero] using h
  calc
    (∫⁻ b, (ENNReal.ofReal ‖(b m - b 0) + ε * (b M - b m) + w‖) ^ (-a) *
        (ENNReal.ofReal ‖b M - b m‖) ^ (-k) ∂(planarBrownianMotion x)) =
        ∫⁻ b, g (X b, Y b) ∂P := rfl
    _ = ∫⁻ p, g p ∂(P.map (fun b => (X b, Y b))) := (lintegral_map hg (hX.prodMk hY)).symm
    _ = ∫⁻ p, g p ∂((P.map X).prod (P.map Y)) := by rw [hlaw]
    _ = ∫⁻ v, ∫⁻ u, g (u, v) ∂(P.map X) ∂(P.map Y) := lintegral_prod_symm _ hg.aemeasurable
    _ = ∫⁻ v, (∫⁻ u, (ENNReal.ofReal ‖u + ε * v + w‖) ^ (-a) ∂(P.map X)) *
        (ENNReal.ofReal ‖v‖) ^ (-k) ∂(P.map Y) := by
      congr 1
      funext v
      have hmeas : Measurable (fun u : ℂ => (ENNReal.ofReal ‖u + ε * v + w‖) ^ (-a)) := by
        fun_prop
      show (∫⁻ u, (ENNReal.ofReal ‖u + ε * v + w‖) ^ (-a) * (ENNReal.ofReal ‖v‖) ^ (-k)
        ∂(P.map X)) = _
      exact lintegral_mul_const _ hmeas
    _ ≤ ∫⁻ v, K₁ * (ENNReal.ofReal ‖v‖) ^ (-k) ∂(P.map Y) := by
      apply lintegral_mono
      intro v
      exact mul_le_mul_of_nonneg_right (hX1 v) zero_le
    _ = K₁ * ∫⁻ v, (ENNReal.ofReal ‖v‖) ^ (-k) ∂(P.map Y) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ K₁ * K₂ := mul_le_mul_of_nonneg_left hY1 zero_le

/-- The expected singular weight at one time against a Riesz kernel at a second time is
bounded by inverse powers of the earlier time and of the time difference. -/
theorem lintegral_planarBrownianMotion_singular_increment_le (x z : ℂ) {s t : ℝ≥0}
    (hst : s ≠ t) (hm : min s t ≠ 0) {a k c e : ℝ} (ha : 0 < a) (hac : a < 2 * c)
    (hc1 : c < 1) (hk : 0 < k) (hke : k < 2 * e) (he1 : e < 1) :
    (∫⁻ b, (ENNReal.ofReal ‖b s - z‖) ^ (-a) * (ENNReal.ofReal ‖b s - b t‖) ^ (-k)
      ∂(planarBrownianMotion x)) ≤
      ENNReal.ofReal (1 + (2 / Real.pi) ^ c * 2 ^ (2 * c) * ((min s t : ℝ≥0) : ℝ) ^ (-c) *
        (a / (2 * c - a))) *
      ENNReal.ofReal (1 + (2 / Real.pi) ^ e * 2 ^ (2 * e) * |(s : ℝ) - (t : ℝ)| ^ (-e) *
        (k / (2 * e - k))) := by
  rcases lt_or_gt_of_ne hst with h | h
  · have hmin : min s t = s := min_eq_left h.le
    rw [hmin] at hm ⊢
    have heq : (∫⁻ b, (ENNReal.ofReal ‖b s - z‖) ^ (-a) * (ENNReal.ofReal ‖b s - b t‖) ^ (-k)
        ∂(planarBrownianMotion x)) =
        ∫⁻ b, (ENNReal.ofReal ‖(b s - b 0) + 0 * (b t - b s) + (x - z)‖) ^ (-a) *
          (ENNReal.ofReal ‖b t - b s‖) ^ (-k) ∂(planarBrownianMotion x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with b hb
      rw [hb, norm_sub_rev (b s) (b t)]
      have h1 : b s - z = (b s - x) + 0 * (b t - b s) + (x - z) := by ring
      rw [h1]
    rw [heq, abs_sub_comm]
    exact lintegral_planarBrownianMotion_shifted_increment_pair_le x (x - z) 0 h hm
      ha hac hc1 hk hke he1
  · have hmin : min s t = t := min_eq_right h.le
    rw [hmin] at hm ⊢
    have heq : (∫⁻ b, (ENNReal.ofReal ‖b s - z‖) ^ (-a) * (ENNReal.ofReal ‖b s - b t‖) ^ (-k)
        ∂(planarBrownianMotion x)) =
        ∫⁻ b, (ENNReal.ofReal ‖(b t - b 0) + 1 * (b s - b t) + (x - z)‖) ^ (-a) *
          (ENNReal.ofReal ‖b s - b t‖) ^ (-k) ∂(planarBrownianMotion x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with b hb
      rw [hb]
      have h1 : b s - z = (b t - x) + 1 * (b s - b t) + (x - z) := by ring
      rw [h1]
    rw [heq]
    exact lintegral_planarBrownianMotion_shifted_increment_pair_le x (x - z) 1 h hm
      ha hac hc1 hk hke he1

/-- The unit-time measure has no atoms. -/
theorem nullSingletonClass_unit_time :
    NullSingletonClass (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) := by
  constructor
  intro t
  rw [Measure.map_apply continuous_real_toNNReal.measurable (measurableSet_singleton t),
    Measure.restrict_apply (continuous_real_toNNReal.measurable (measurableSet_singleton t))]
  apply measure_mono_null _ (measure_singleton (t : ℝ))
  intro a ha
  have ht := congrArg (fun v : ℝ≥0 => (v : ℝ)) ha.1
  have ha0 : 0 ≤ a := ha.2.1
  simpa [Real.toNNReal_of_nonneg ha0] using ht

/-- Unit-time parameters are almost surely at most one. -/
theorem ae_unit_time_le_one :
    ∀ᵐ t : ℝ≥0 ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))), (t : ℝ) ≤ 1 := by
  have hs : MeasurableSet {t : ℝ≥0 | (t : ℝ) ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [ae_map_iff continuous_real_toNNReal.measurable.aemeasurable hs]
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  simpa [Real.toNNReal_of_nonneg hr.1] using hr.2

/-- The product of an inverse power of the earlier time and a subcritical time-difference
kernel is integrable on the unit square. -/
theorem lintegral_unit_time_min_rpow_mul_abs_sub_rpow_lt_top {c e : ℝ} (hc0 : 0 < c)
    (hc1 : c < 1) (he0 : 0 < e) (he1 : e < 1) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) *
      ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e)) ∂(ν.prod ν)) < ∞ := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  obtain ⟨Kc, hKc, hc⟩ := exists_uniform_unit_time_rpow_bound hc0 hc1
  obtain ⟨Ke, hKe, he⟩ := exists_uniform_unit_time_rpow_bound he0 he1
  let f : ℝ≥0 → ℝ≥0∞ := fun s => ENNReal.ofReal ((s : ℝ) ^ (-c))
  let k : ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun p => ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e))
  have hf : Measurable f := by fun_prop
  have hk : Measurable k := by fun_prop
  have hf0 : (∫⁻ s, f s ∂ν) ≤ Kc := by
    have h := hc 0 (by norm_num)
    simpa [f] using h
  have hk1 : ∀ᵐ s ∂ν, (∫⁻ t, k (s, t) ∂ν) ≤ Ke := by
    filter_upwards [ae_unit_time_le_one] with s hs
    have h := he s hs
    have heq : (fun t : ℝ≥0 => k (s, t)) =
        fun t : ℝ≥0 => ENNReal.ofReal (|(t : ℝ) - (s : ℝ)| ^ (-e)) := by
      funext t
      simp only [k, abs_sub_comm]
    rw [heq]
    exact h
  have hk2 : ∀ᵐ t ∂ν, (∫⁻ s, k (s, t) ∂ν) ≤ Ke := by
    filter_upwards [ae_unit_time_le_one] with t ht
    exact he t ht
  have hpoint : ∀ p : ℝ≥0 × ℝ≥0,
      ENNReal.ofReal (((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) * k p ≤
        f p.1 * k p + f p.2 * k p := by
    intro p
    rcases min_choice p.1 p.2 with h | h
    · rw [h]
      exact le_self_add
    · rw [h]
      exact le_add_self
  have hI1 : (∫⁻ p, f p.1 * k p ∂(ν.prod ν)) ≤ Kc * Ke := by
    have hm1 : Measurable (fun p : ℝ≥0 × ℝ≥0 => f p.1 * k p) := (hf.comp measurable_fst).mul hk
    rw [lintegral_prod _ hm1.aemeasurable]
    calc
      (∫⁻ s, ∫⁻ t, f (s, t).1 * k (s, t) ∂ν ∂ν) = ∫⁻ s, f s * ∫⁻ t, k (s, t) ∂ν ∂ν := by
        congr 1
        funext s
        have hks : Measurable (fun t : ℝ≥0 => k (s, t)) := hk.comp measurable_prodMk_left
        exact lintegral_const_mul (f s) hks
      _ ≤ ∫⁻ s, f s * Ke ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hk1] with s hs
        exact mul_le_mul_of_nonneg_left hs zero_le
      _ = (∫⁻ s, f s ∂ν) * Ke := lintegral_mul_const _ hf
      _ ≤ Kc * Ke := mul_le_mul_of_nonneg_right hf0 zero_le
  have hI2 : (∫⁻ p, f p.2 * k p ∂(ν.prod ν)) ≤ Kc * Ke := by
    have hm2 : Measurable (fun p : ℝ≥0 × ℝ≥0 => f p.2 * k p) := (hf.comp measurable_snd).mul hk
    rw [lintegral_prod_symm _ hm2.aemeasurable]
    calc
      (∫⁻ t, ∫⁻ s, f (s, t).2 * k (s, t) ∂ν ∂ν) = ∫⁻ t, f t * ∫⁻ s, k (s, t) ∂ν ∂ν := by
        congr 1
        funext t
        have hkt : Measurable (fun s : ℝ≥0 => k (s, t)) := hk.comp measurable_prodMk_right
        exact lintegral_const_mul (f t) hkt
      _ ≤ ∫⁻ t, f t * Ke ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hk2] with t ht
        exact mul_le_mul_of_nonneg_left ht zero_le
      _ = (∫⁻ t, f t ∂ν) * Ke := lintegral_mul_const _ hf
      _ ≤ Kc * Ke := mul_le_mul_of_nonneg_right hf0 zero_le
  calc
    (∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) * k p ∂(ν.prod ν)) ≤
        ∫⁻ p, f p.1 * k p + f p.2 * k p ∂(ν.prod ν) := lintegral_mono hpoint
    _ = (∫⁻ p, f p.1 * k p ∂(ν.prod ν)) + ∫⁻ p, f p.2 * k p ∂(ν.prod ν) :=
      lintegral_add_left ((hf.comp measurable_fst).mul hk) _
    _ ≤ Kc * Ke + Kc * Ke := add_le_add hI1 hI2
    _ < ∞ := ENNReal.add_lt_top.mpr
      ⟨ENNReal.mul_lt_top hKc hKe, ENNReal.mul_lt_top hKc hKe⟩

private theorem one_add_mul_rpow_le {v c G : ℝ} (hv : 0 < v) (hv1 : v ≤ 1) (hc : 0 ≤ c)
    (B : ℝ) (hB : B = G * v ^ (-c)) :
    1 + B ≤ (1 + G) * v ^ (-c) := by
  have h1 : 1 ≤ v ^ (-c) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hv hv1 (by linarith)
  rw [hB]
  nlinarith

/-- The expected unit-time singular occupation is bounded uniformly over the start and the
centre below dimension two. -/
theorem exists_planarBrownianMotion_unit_singular_occupation_le {a : ℝ} (ha0 : 0 < a)
    (ha2 : a < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x z : ℂ,
      (∫⁻ b, ∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-a) ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
        ∂(planarBrownianMotion x)) ≤ C := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let : NullSingletonClass ν := nullSingletonClass_unit_time
  let c : ℝ := (a + 2) / 4
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hac : a < 2 * c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  let G : ℝ := (2 / Real.pi) ^ c * 2 ^ (2 * c) * (a / (2 * c - a))
  have hG : 0 ≤ G := by
    have : 0 < 2 * c - a := by linarith
    dsimp [G]; positivity
  obtain ⟨K, hK, hKb⟩ := exists_uniform_unit_time_rpow_bound hc0 hc1
  refine ⟨ENNReal.ofReal (1 + G) * K, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK,
    fun x z => ?_⟩
  have hmeas : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 =>
      (ENNReal.ofReal ‖q.1 q.2 - z‖) ^ (-a)) := by fun_prop
  change (∫⁻ b, ∫⁻ t, (ENNReal.ofReal ‖b t - z‖) ^ (-a) ∂ν ∂(planarBrownianMotion x)) ≤ _
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have hpt : ∀ᵐ t ∂ν, (∫⁻ b, (ENNReal.ofReal ‖b t - z‖) ^ (-a) ∂(planarBrownianMotion x)) ≤
      ENNReal.ofReal (1 + G) *
        ENNReal.ofReal (|(t : ℝ) - ((0 : ℝ≥0) : ℝ)| ^ (-c)) := by
    filter_upwards [ν.ae_ne 0, ae_unit_time_le_one] with t ht0 ht1
    have hm : Measurable (fun b : ContinuousPath ℂ => b t - b 0) :=
      (ContinuousPath.measurable_coordinateProcess _).sub
        (ContinuousPath.measurable_coordinateProcess _)
    have heq : (∫⁻ b, (ENNReal.ofReal ‖b t - z‖) ^ (-a) ∂(planarBrownianMotion x)) =
        ∫⁻ u, (ENNReal.ofReal ‖u - (z - x)‖) ^ (-a)
          ∂((planarBrownianMotion x).map (fun b : ContinuousPath ℂ => b t - b 0)) := by
      rw [lintegral_map (by fun_prop) hm]
      apply lintegral_congr_ae
      filter_upwards [ae_planarBrownianMotion_eval_zero x] with b hb
      rw [hb]
      congr 3
      ring
    rw [heq]
    refine (lintegral_map_increment_enorm_sub_rpow_neg_le x (z - x) (s := 0) (t := t) ht0
      ha0 hac hc1).trans ?_
    have htpos : 0 < |(t : ℝ) - ((0 : ℝ≥0) : ℝ)| := by
      rw [NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)]
      exact lt_of_le_of_ne (NNReal.coe_nonneg t) (fun h => ht0 (NNReal.coe_injective h.symm))
    have ht1' : |(t : ℝ) - ((0 : ℝ≥0) : ℝ)| ≤ 1 := by
      rw [NNReal.coe_zero, sub_zero, abs_of_nonneg (NNReal.coe_nonneg t)]
      exact ht1
    have hb := one_add_mul_rpow_le (G := G) htpos ht1' hc0.le
      ((2 / Real.pi) ^ c * 2 ^ (2 * c) * |(t : ℝ) - ((0 : ℝ≥0) : ℝ)| ^ (-c) * (a / (2 * c - a)))
      (by dsimp [G]; ring)
    rw [← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal hb
  calc
    (∫⁻ t, ∫⁻ b, (ENNReal.ofReal ‖b t - z‖) ^ (-a) ∂(planarBrownianMotion x) ∂ν) ≤
        ∫⁻ t, ENNReal.ofReal (1 + G) *
          ENNReal.ofReal (|(t : ℝ) - ((0 : ℝ≥0) : ℝ)| ^ (-c)) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal (1 + G) *
        ∫⁻ t, ENNReal.ofReal (|(t : ℝ) - ((0 : ℝ≥0) : ℝ)| ^ (-c)) ∂ν :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (1 + G) * K := by
      gcongr
      exact hKb 0 (by norm_num)

/-- The expected unit-time singular energy with a Riesz kernel is bounded uniformly over the
start and the centre, below dimension two in both exponents. -/
theorem exists_planarBrownianMotion_unit_singular_riesz_energy_le {a k : ℝ}
    (ha0 : 0 < a) (ha2 : a < 2) (hk0 : 0 < k) (hk2 : k < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x z : ℂ,
      (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖b p.1 - z‖) ^ (-a) *
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-k) ∂((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).prod (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))
          ∂(planarBrownianMotion x)) ≤ C := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν1 : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν1⟩
  let : NullSingletonClass ν := nullSingletonClass_unit_time
  let c : ℝ := (a + 2) / 4
  let e : ℝ := (k + 2) / 4
  have hc0 : 0 < c := by dsimp [c]; linarith
  have hac : a < 2 * c := by dsimp [c]; linarith
  have hc1 : c < 1 := by dsimp [c]; linarith
  have he0 : 0 < e := by dsimp [e]; linarith
  have hke : k < 2 * e := by dsimp [e]; linarith
  have he1 : e < 1 := by dsimp [e]; linarith
  let G₁ : ℝ := (2 / Real.pi) ^ c * 2 ^ (2 * c) * (a / (2 * c - a))
  let G₂ : ℝ := (2 / Real.pi) ^ e * 2 ^ (2 * e) * (k / (2 * e - k))
  have hG₁ : 0 ≤ G₁ := by
    have : 0 < 2 * c - a := by linarith
    dsimp [G₁]; positivity
  have hG₂ : 0 ≤ G₂ := by
    have : 0 < 2 * e - k := by linarith
    dsimp [G₂]; positivity
  have htime := lintegral_unit_time_min_rpow_mul_abs_sub_rpow_lt_top hc0 hc1 he0 he1
  refine ⟨ENNReal.ofReal ((1 + G₁) * (1 + G₂)) *
      ∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) *
        ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e)) ∂(ν.prod ν),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top htime, ?_⟩
  intro x z
  let F : ContinuousPath ℂ → ℝ≥0 × ℝ≥0 → ℝ≥0∞ := fun b p =>
    (ENNReal.ofReal ‖b p.1 - z‖) ^ (-a) * (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-k)
  have hF : Measurable (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hdiag : ∀ᵐ p ∂(ν.prod ν), p.1 ≠ p.2 := by
    rw [ae_iff]
    simp only [ne_eq, not_not]
    rw [Measure.prod_apply (measurableSet_eq_fun measurable_fst measurable_snd)]
    have hpre (s : ℝ≥0) : Prod.mk s ⁻¹' {p : ℝ≥0 × ℝ≥0 | p.1 = p.2} = {s} := by
      ext t
      simp [eq_comm]
    simp [hpre]
  have hfst : ∀ᵐ p ∂(ν.prod ν), p.1 ≠ 0 ∧ (p.1 : ℝ) ≤ 1 :=
    (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae
      ((ν.ae_ne 0).and ae_unit_time_le_one)
  have hsnd : ∀ᵐ p ∂(ν.prod ν), p.2 ≠ 0 ∧ (p.2 : ℝ) ≤ 1 :=
    (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae
      ((ν.ae_ne 0).and ae_unit_time_le_one)
  have hbound : ∀ᵐ p ∂(ν.prod ν), (∫⁻ b, F b p ∂(planarBrownianMotion x)) ≤
      ENNReal.ofReal ((1 + G₁) * (1 + G₂)) *
        (ENNReal.ofReal (((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) *
          ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e))) := by
    filter_upwards [hdiag, hfst, hsnd] with p hp h1 h2
    have hmin0 : min p.1 p.2 ≠ 0 := by
      rcases min_choice p.1 p.2 with h | h <;> rw [h]
      · exact h1.1
      · exact h2.1
    have hminpos : 0 < ((min p.1 p.2 : ℝ≥0) : ℝ) := by
      have := pos_iff_ne_zero.mpr hmin0
      exact_mod_cast this
    have hmin1 : ((min p.1 p.2 : ℝ≥0) : ℝ) ≤ 1 := by
      rcases min_choice p.1 p.2 with h | h <;> rw [h]
      · exact h1.2
      · exact h2.2
    have hdpos : 0 < |(p.1 : ℝ) - (p.2 : ℝ)| := by
      apply abs_pos.mpr
      exact sub_ne_zero.mpr (fun h => hp (NNReal.coe_injective h))
    have hd1 : |(p.1 : ℝ) - (p.2 : ℝ)| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [h1.2, h2.2, p.1.2, p.2.2]
    have hb := lintegral_planarBrownianMotion_singular_increment_le x z hp hmin0
      ha0 hac hc1 hk0 hke he1
    have hK₁ := one_add_mul_rpow_le (G := G₁) hminpos hmin1 hc0.le
      ((2 / Real.pi) ^ c * 2 ^ (2 * c) * ((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c) * (a / (2 * c - a)))
      (by dsimp [G₁]; ring)
    have hK₂ := one_add_mul_rpow_le (G := G₂) hdpos hd1 he0.le
      ((2 / Real.pi) ^ e * 2 ^ (2 * e) * |(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e) * (k / (2 * e - k)))
      (by dsimp [G₂]; ring)
    calc
      (∫⁻ b, F b p ∂(planarBrownianMotion x)) ≤ _ := hb
      _ ≤ ENNReal.ofReal ((1 + G₁) * ((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) *
          ENNReal.ofReal ((1 + G₂) * |(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hK₁) (ENNReal.ofReal_le_ofReal hK₂)
      _ = _ := by
        have hA : 0 ≤ 1 + G₁ := by linarith
        have hB : 0 ≤ 1 + G₂ := by linarith
        rw [ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB, ENNReal.ofReal_mul (by positivity)]
        ring
  change (∫⁻ b, ∫⁻ p, F b p ∂(ν.prod ν) ∂(planarBrownianMotion x)) ≤ _
  rw [lintegral_lintegral_swap hF.aemeasurable]
  calc
    (∫⁻ p, ∫⁻ b, F b p ∂(planarBrownianMotion x) ∂(ν.prod ν)) ≤
        ∫⁻ p, ENNReal.ofReal ((1 + G₁) * (1 + G₂)) *
          (ENNReal.ofReal (((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) *
            ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e))) ∂(ν.prod ν) :=
      lintegral_mono_ae hbound
    _ = ENNReal.ofReal ((1 + G₁) * (1 + G₂)) *
        ∫⁻ p, ENNReal.ofReal (((min p.1 p.2 : ℝ≥0) : ℝ) ^ (-c)) *
          ENNReal.ofReal (|(p.1 : ℝ) - (p.2 : ℝ)| ^ (-e)) ∂(ν.prod ν) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The expected unit-time singular energy with a Riesz kernel is finite below dimension two
in both exponents. -/
theorem planarBrownianMotion_unit_singular_riesz_energy_lt_top (x z : ℂ) {a k : ℝ}
    (ha0 : 0 < a) (ha2 : a < 2) (hk0 : 0 < k) (hk2 : k < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    (∫⁻ b, ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖b p.1 - z‖) ^ (-a) *
      (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-k) ∂(ν.prod ν) ∂(planarBrownianMotion x)) < ∞ := by
  obtain ⟨C, hC, h⟩ := exists_planarBrownianMotion_unit_singular_riesz_energy_le ha0 ha2 hk0 hk2
  exact (h x z).trans_lt hC

private theorem ofReal_rpow_neg_le_two_rpow_mul {r s q : ℝ} (hr : 0 < r) (hrs : r ≤ 2 * s)
    (hq : 0 ≤ q) :
    (ENNReal.ofReal s) ^ (-q) ≤ 2 ^ q * (ENNReal.ofReal r) ^ (-q) := by
  have hs : 0 < s := by linarith
  rw [ENNReal.ofReal_rpow_of_pos hs, ENNReal.ofReal_rpow_of_pos hr]
  have h2 : (2 : ℝ≥0∞) ^ q = ENNReal.ofReal ((2 : ℝ) ^ q) := by
    rw [← ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [h2, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have heq : (r / 2) ^ (-q) = 2 ^ q * r ^ (-q) := by
    rw [Real.div_rpow hr.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_inv_eq_mul, mul_comm]
  calc
    s ^ (-q) ≤ (r / 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    _ = 2 ^ q * r ^ (-q) := heq

/-- A triangle-inequality bound for the singular weighted pair kernel. -/
theorem enorm_rpow_neg_weighted_pair_le (u v : ℂ) {q β : ℝ} (hq : 0 < q) (hβ : 0 < β) :
    (ENNReal.ofReal ‖u‖) ^ (-q) * (ENNReal.ofReal ‖v‖) ^ (-q) *
        (ENNReal.ofReal ‖u - v‖) ^ (-β) ≤
      2 ^ q * ((ENNReal.ofReal ‖u‖) ^ (-q) + (ENNReal.ofReal ‖v‖) ^ (-q)) *
        (ENNReal.ofReal ‖u - v‖) ^ (-(q + β)) := by
  set A := ENNReal.ofReal ‖u‖
  set B := ENNReal.ofReal ‖v‖
  set D := ENNReal.ofReal ‖u - v‖
  have hAt : A ≠ ⊤ := ENNReal.ofReal_ne_top
  have hBt : B ≠ ⊤ := ENNReal.ofReal_ne_top
  have hDt : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hA0 : A ^ (-q) ≠ 0 := by
    intro h
    rw [ENNReal.rpow_eq_zero_iff] at h
    rcases h with h | h
    · linarith [h.2]
    · exact hAt h.1
  by_cases hD : ‖u - v‖ = 0
  · have hD0 : D = 0 := by
      change ENNReal.ofReal ‖u - v‖ = 0
      rw [hD, ENNReal.ofReal_zero]
    have htop : D ^ (-(q + β)) = ⊤ := by
      rw [hD0]
      exact ENNReal.zero_rpow_of_neg (by linarith)
    rw [htop]
    have hne : 2 ^ q * (A ^ (-q) + B ^ (-q)) ≠ 0 := by
      apply mul_ne_zero
      · exact (ENNReal.rpow_pos (by norm_num) (by norm_num)).ne'
      · exact fun h => hA0 (le_antisymm (h ▸ le_self_add) bot_le)
    rw [ENNReal.mul_top hne]
    exact le_top
  · have hDpos : 0 < ‖u - v‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hD)
    have hD0 : D ≠ 0 := (ENNReal.ofReal_pos.mpr hDpos).ne'
    have hsplit : D ^ (-(q + β)) = D ^ (-q) * D ^ (-β) := by
      rw [show -(q + β) = -q + -β by ring, ENNReal.rpow_add _ _ hD0 hDt]
    have htri := norm_sub_le u v
    rcases le_total ‖v‖ ‖u‖ with h | h
    · have hAD : A ^ (-q) ≤ 2 ^ q * D ^ (-q) :=
        ofReal_rpow_neg_le_two_rpow_mul hDpos (by linarith) hq.le
      calc
        A ^ (-q) * B ^ (-q) * D ^ (-β) ≤ (2 ^ q * D ^ (-q)) * B ^ (-q) * D ^ (-β) := by
          gcongr
        _ = 2 ^ q * B ^ (-q) * D ^ (-(q + β)) := by
          rw [hsplit]
          ring
        _ ≤ 2 ^ q * (A ^ (-q) + B ^ (-q)) * D ^ (-(q + β)) := by
          gcongr
          exact le_add_self
    · have hBD : B ^ (-q) ≤ 2 ^ q * D ^ (-q) :=
        ofReal_rpow_neg_le_two_rpow_mul hDpos (by linarith) hq.le
      calc
        A ^ (-q) * B ^ (-q) * D ^ (-β) ≤ A ^ (-q) * (2 ^ q * D ^ (-q)) * D ^ (-β) := by
          gcongr
        _ = 2 ^ q * A ^ (-q) * D ^ (-(q + β)) := by
          rw [hsplit]
          ring
        _ ≤ 2 ^ q * (A ^ (-q) + B ^ (-q)) * D ^ (-(q + β)) := by
          gcongr
          exact le_self_add

/-- The singularly weighted unit-time pair energy with a Riesz kernel. -/
noncomputable def unitSingularWeightedPairEnergy (z : ℂ) (q β : ℝ)
    (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
    (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) * (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν)

/-- The weighted pair energy is measurable in the path. -/
theorem measurable_unitSingularWeightedPairEnergy (z : ℂ) (q β : ℝ) :
    Measurable (unitSingularWeightedPairEnergy z q β) := by
  unfold unitSingularWeightedPairEnergy
  apply Measurable.lintegral_prod_right
  fun_prop

/-- The singularly weighted pair energy has expectation bounded uniformly over the start and
the centre when `q + β < 2`. -/
theorem exists_planarBrownianMotion_unitSingularWeightedPairEnergy_le {q β : ℝ}
    (hq : 0 < q) (hβ : 0 < β) (hqβ : q + β < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ x z : ℂ,
      (∫⁻ b, unitSingularWeightedPairEnergy z q β b ∂(planarBrownianMotion x)) ≤ C := by
  obtain ⟨C₀, hC₀, hC₀le⟩ := exists_planarBrownianMotion_unit_singular_riesz_energy_le hq
    (by linarith) (show 0 < q + β by linarith) hqβ
  refine ⟨2 ^ q * (2 * C₀), ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg hq.le (by norm_num)) (ENNReal.mul_lt_top (by norm_num) hC₀),
    fun x z => ?_⟩
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let I : ContinuousPath ℂ → ℝ≥0∞ := fun b => ∫⁻ p : ℝ≥0 × ℝ≥0,
    (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) * (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(q + β))
      ∂(ν.prod ν)
  have hI : (∫⁻ b, I b ∂(planarBrownianMotion x)) ≤ C₀ := hC₀le x z
  have hpoint (b : ContinuousPath ℂ) :
      unitSingularWeightedPairEnergy z q β b ≤ 2 ^ q * (I b + I b) := by
    have hm1 : Measurable (fun p : ℝ≥0 × ℝ≥0 =>
        (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) * (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(q + β))) := by
      fun_prop
    have hm2 : Measurable (fun p : ℝ≥0 × ℝ≥0 =>
        (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) * (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(q + β))) := by
      fun_prop
    have hswap : (∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) *
        (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(q + β)) ∂(ν.prod ν)) = I b := by
      rw [← lintegral_prod_swap]
      apply lintegral_congr
      intro p
      simp only [Prod.fst_swap, Prod.snd_swap, norm_sub_rev (b p.2) (b p.1)]
    unfold unitSingularWeightedPairEnergy
    calc
      _ ≤ ∫⁻ p : ℝ≥0 × ℝ≥0, 2 ^ q * ((ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) *
            (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(q + β)) +
          (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) *
            (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-(q + β))) ∂(ν.prod ν) := by
        apply lintegral_mono
        intro p
        have h := enorm_rpow_neg_weighted_pair_le (b p.1 - z) (b p.2 - z) hq hβ
        rw [sub_sub_sub_cancel_right] at h
        calc
          _ ≤ _ := h
          _ = _ := by ring
      _ = 2 ^ q * (I b + I b) := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le (by norm_num)),
          lintegral_add_left hm1, hswap]
  calc
    (∫⁻ b, unitSingularWeightedPairEnergy z q β b ∂(planarBrownianMotion x)) ≤
        ∫⁻ b, 2 ^ q * (I b + I b) ∂(planarBrownianMotion x) := lintegral_mono hpoint
    _ = 2 ^ q * (2 * ∫⁻ b, I b ∂(planarBrownianMotion x)) := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le (by norm_num))]
      simp_rw [← two_mul]
      rw [lintegral_const_mul' _ _ (by norm_num)]
    _ ≤ 2 ^ q * (2 * C₀) := by gcongr

/-- The singularly weighted pair energy has finite expectation when `q + β < 2`. -/
theorem planarBrownianMotion_unitSingularWeightedPairEnergy_lt_top (x z : ℂ) {q β : ℝ}
    (hq : 0 < q) (hβ : 0 < β) (hqβ : q + β < 2) :
    (∫⁻ b, unitSingularWeightedPairEnergy z q β b ∂(planarBrownianMotion x)) < ∞ := by
  obtain ⟨C, hC, h⟩ := exists_planarBrownianMotion_unitSingularWeightedPairEnergy_le hq hβ hqβ
  exact (h x z).trans_lt hC

/-- The real part of the weighted pair energy. -/
noncomputable def unitSingularWeightedPairEnergyReal (z : ℂ) (q β : ℝ)
    (b : ContinuousPath ℂ) : ℝ :=
  (unitSingularWeightedPairEnergy z q β b).toReal

/-- The real weighted pair energy is Brownian integrable when `q + β < 2`. -/
theorem integrable_unitSingularWeightedPairEnergyReal (x z : ℂ) {q β : ℝ}
    (hq : 0 < q) (hβ : 0 < β) (hqβ : q + β < 2) :
    Integrable (unitSingularWeightedPairEnergyReal z q β) (planarBrownianMotion x) :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_unitSingularWeightedPairEnergy z q β).aemeasurable
    (planarBrownianMotion_unitSingularWeightedPairEnergy_lt_top x z hq hβ hqβ).ne

/-- Every near-diagonal singular pair occupation at radius `r` is bounded by `r ^ β`
times the weighted pair energy. -/
theorem unitSingularPairNear_le_rpow_mul_weightedPairEnergy (z : ℂ) {q β r : ℝ}
    (hβ : 0 < β) (hr : 0 < r) (b : ContinuousPath ℂ) :
    unitSingularPairNear z q r b ≤
      ENNReal.ofReal (r ^ β) * unitSingularWeightedPairEnergy z q β b := by
  unfold unitSingularPairNear unitSingularWeightedPairEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro p
  dsimp only
  split_ifs with h
  · have hr0 : ENNReal.ofReal r ≠ 0 := by simpa using hr
    have hle : ENNReal.ofReal ‖b p.1 - b p.2‖ ≤ ENNReal.ofReal r :=
      ENNReal.ofReal_le_ofReal h.le
    have hanti : (ENNReal.ofReal r) ^ (-β) ≤ (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) := by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hle hβ.le)
    have hone : 1 ≤ ENNReal.ofReal (r ^ β) * (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) := by
      calc
        (1 : ℝ≥0∞) = ENNReal.ofReal (r ^ β) * (ENNReal.ofReal r) ^ (-β) := by
          rw [← ENNReal.ofReal_rpow_of_pos hr, ENNReal.rpow_neg,
            ENNReal.mul_inv_cancel (by simpa using (ENNReal.rpow_pos (by simpa using hr)
              ENNReal.ofReal_ne_top).ne')
              (ENNReal.rpow_ne_top_of_nonneg hβ.le ENNReal.ofReal_ne_top)]
        _ ≤ _ := mul_le_mul_of_nonneg_left hanti zero_le
    calc
      (ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) * (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q) =
          1 * ((ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) * (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q)) :=
        (one_mul _).symm
      _ ≤ (ENNReal.ofReal (r ^ β) * (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β)) *
          ((ENNReal.ofReal ‖b p.1 - z‖) ^ (-q) * (ENNReal.ofReal ‖b p.2 - z‖) ^ (-q)) :=
        mul_le_mul_of_nonneg_right hone zero_le
      _ = _ := by ring
  · exact zero_le

/-- For almost every Brownian path, the real weighted pair energy is an all-radius envelope
for the near-diagonal singular pair occupations. -/
theorem planarBrownianMotion_ae_unitSingularPairNear_le_weightedPairEnergy (x z : ℂ)
    {q β : ℝ} (hq : 0 < q) (hβ : 0 < β) (hqβ : q + β < 2) :
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r →
      unitSingularPairNear z q r b ≤
        ENNReal.ofReal (unitSingularWeightedPairEnergyReal z q β b) * ENNReal.ofReal (r ^ β) := by
  filter_upwards [ae_lt_top (measurable_unitSingularWeightedPairEnergy z q β)
    (planarBrownianMotion_unitSingularWeightedPairEnergy_lt_top x z hq hβ hqβ).ne] with b hb r hr
  rw [unitSingularWeightedPairEnergyReal, ENNReal.ofReal_toReal hb.ne, mul_comm]
  exact unitSingularPairNear_le_rpow_mul_weightedPairEnergy z hβ hr b

end HarmonicBalls
