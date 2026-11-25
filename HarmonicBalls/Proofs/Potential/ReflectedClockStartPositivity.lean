import HarmonicBalls.Proofs.Potential.ReflectedClockIdentification
import HarmonicBalls.Proofs.Potential.ReflectedSquareScaling

/-!
# The clock of reflected Brownian motion charges every initial time interval

Let `F x` be an LQG clock of reflected Brownian motion in the square `K = closedSquare a L` from
`x` and `G x` an LQG clock of planar Brownian motion from `x`, for the same circle averages. While
the planar path stays in `K`, the folded path is the planar path, so the approximating clocks of
the two coincide, and so do the two limits: almost surely, `F (fold ∘ ω) = G ω` on `[0, T]` on
the event that `ω` stays in `K` up to time `T` (`ae_isLQGClock_reflected_eq_planar`). From a start
in the interior of `K` the planar path stays in `K` for a positive time, and the planar clock is
strictly increasing from `0` (Proposition 2.5, `exists_ae_forall_isLQGClock_isTimeChangeClock`),
so the reflected clock is positive at every positive time. This is the agreement of the stopped
reflected clock with the planar Liouville clock on a disk compactly contained in the square
(Fukushima–Oshima–Takeda (2011), Theorem 5.1.7 for the uniqueness of the clock of the killed
process; Garban–Rhodes–Vargas (2016), Theorem 2.7), read at the initial time only.

For the clock `A` of reflected Brownian motion in the unit square obtained from the clocks `F x`
by scaling (`exists_isUnitSquarePCAF_of_isLQGClock`), this gives `0 < A u` for every `u > 0`,
almost surely from every start in the interior of `K₀` (`ae_pos_unitSquareClock_of_mem_interior`),
and from almost every start for the normalized measure when the frontier of `K` is null
(`ae_ae_forall_pos_unitSquareClock`).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess Metric
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- The approximating LQG clock up to time `t` depends only on the path up to time `t`. -/
theorem lqgClockApprox_eq_of_eqOn {γ : ℝ} {hε : ℝ → ℂ → ℝ} {ε : ℝ} {b b' : ContinuousPath ℂ}
    {T : ℝ≥0} (hbb : ∀ u ≤ T, b u = b' u) {t : ℝ≥0} (ht : t ≤ T) :
    lqgClockApprox γ hε ε b t = lqgClockApprox γ hε ε b' t := by
  unfold lqgClockApprox
  refine intervalIntegral.integral_congr fun s hs => ?_
  have hs' : s ∈ Icc (0 : ℝ) t := by rwa [uIcc_of_le t.coe_nonneg] at hs
  have hst : s.toNNReal ≤ T := (Real.toNNReal_le_iff_le_coe.2 hs'.2).trans ht
  simp only [hbb s.toNNReal hst]

/-- **The reflected clock is the planar clock while the planar path stays in the square.** -/
theorem ae_isLQGClock_reflected_eq_planar {γ : ℝ} {hε : ℝ → ℂ → ℝ} {a : ℂ} {L : ℝ} (hL : 0 < L)
    {x : ℂ} {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock (reflectedPlanarBrownianMotion a L) γ hε x F)
    (hG : IsLQGClock planarBrownianMotion γ hε x G) (T : ℝ≥0) :
    ∀ᵐ ω ∂planarBrownianMotion x, (∀ u ≤ T, ω u ∈ closedSquare a L) →
      ∀ t ≤ T, F ((squareFoldCM a L).comp ω) t = G ω t := by
  have hfm := measurable_comp_squareFoldCM a L
  have hQ : reflectedPlanarBrownianMotion a L x =
      (planarBrownianMotion x).map fun ω => (squareFoldCM a L).comp ω :=
    Kernel.map_apply _ hfm x
  have hle : ∀ S : Set (ContinuousPath ℂ),
      planarBrownianMotion x ((fun ω => (squareFoldCM a L).comp ω) ⁻¹' S) ≤
        reflectedPlanarBrownianMotion a L x S := fun S => by
    rw [hQ]
    exact Measure.le_map_apply hfm.aemeasurable S
  set B : ℕ → Set (ContinuousPath ℂ) := fun m => {ω | (∀ u ≤ T, ω u ∈ closedSquare a L) ∧
    ∃ t ≤ T, 2 / ((m : ℝ) + 1) ≤ |F ((squareFoldCM a L).comp ω) t - G ω t|} with hB_def
  have hB : ∀ m, planarBrownianMotion x (B m) = 0 := by
    intro m
    have hη : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have h2eq : (2 : ℝ) / ((m : ℝ) + 1) = 1 / ((m : ℝ) + 1) + 1 / ((m : ℝ) + 1) := by ring
    have hsub : ∀ k : ℕ, B m ⊆ ((fun ω => (squareFoldCM a L).comp ω) ⁻¹'
        {b | ∃ t ≤ T, 1 / ((m : ℝ) + 1) ≤
          |lqgClockApprox γ hε (dyadicScale k) b t - F b t|}) ∪
        {ω | ∃ t ≤ T, 1 / ((m : ℝ) + 1) ≤
          |lqgClockApprox γ hε (dyadicScale k) ω t - G ω t|} := by
      rintro k ω ⟨hω, t, ht, hbad⟩
      have happ : lqgClockApprox γ hε (dyadicScale k) ((squareFoldCM a L).comp ω) t =
          lqgClockApprox γ hε (dyadicScale k) ω t :=
        lqgClockApprox_eq_of_eqOn (fun u hu => squareFold_of_mem a hL (hω u hu)) ht
      by_contra hno
      rw [mem_union, not_or] at hno
      have e1 : |lqgClockApprox γ hε (dyadicScale k) ((squareFoldCM a L).comp ω) t -
          F ((squareFoldCM a L).comp ω) t| < 1 / ((m : ℝ) + 1) :=
        not_le.1 fun h => hno.1 ⟨t, ht, h⟩
      have e2 : |lqgClockApprox γ hε (dyadicScale k) ω t - G ω t| < 1 / ((m : ℝ) + 1) :=
        not_le.1 fun h => hno.2 ⟨t, ht, h⟩
      rw [happ] at e1
      have htri := abs_sub_le (F ((squareFoldCM a L).comp ω) t)
        (lqgClockApprox γ hε (dyadicScale k) ω t) (G ω t)
      rw [abs_sub_comm (F ((squareFoldCM a L).comp ω) t)
        (lqgClockApprox γ hε (dyadicScale k) ω t)] at htri
      linarith
    have hlim := (hF T _ hη).add (hG T _ hη)
    rw [add_zero] at hlim
    refine le_antisymm (ge_of_tendsto' hlim fun k => ?_) zero_le
    exact (measure_mono (hsub k)).trans ((measure_union_le _ _).trans
      (add_le_add (hle _) le_rfl))
  have hall : ∀ᵐ ω ∂planarBrownianMotion x, ∀ m, ω ∉ B m :=
    ae_all_iff.2 fun m => measure_eq_zero_iff_ae_notMem.1 (hB m)
  filter_upwards [hall] with ω hω hK t ht
  by_contra hne
  have hpos : 0 < |F ((squareFoldCM a L).comp ω) t - G ω t| / 2 :=
    half_pos (abs_pos.2 (sub_ne_zero.2 hne))
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hpos
  refine hω m ⟨hK, t, ht, ?_⟩
  have h2 : (2 : ℝ) / ((m : ℝ) + 1) = 2 * (1 / ((m : ℝ) + 1)) := by ring
  rw [h2]
  linarith

/-- **The unit-square clock is positive at positive times from interior starts.** Let `A` be the
clock of reflected Brownian motion in the unit square with `F b s = M A(s / L², Ψ b)` almost
surely from `x`, where `F` is an LQG clock of reflected Brownian motion in `K = closedSquare a L`
from `x` in the interior of `K`, and let `G` be a planar LQG clock from `x` for the same circle
averages, almost surely a time-change clock. Then `0 < A u` almost surely from `(x - a) / L`, for
every `u > 0`. -/
theorem ae_pos_unitSquareClock_of_mem_interior {γ : ℝ} {hε : ℝ → ℂ → ℝ} {a : ℂ} {L : ℝ}
    (hL : 0 < L) {M : ℝ} (hM : 0 < M) {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {x : ℂ} (hx : x ∈ interior (closedSquare a L))
    {F G : ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : IsLQGClock (reflectedPlanarBrownianMotion a L) γ hε x F)
    (hFA : ∀ᵐ b ∂reflectedPlanarBrownianMotion a L x, ∀ s : ℝ≥0,
      F b s = M * (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ))
    (hG : IsLQGClock planarBrownianMotion γ hε x G)
    (hGs : ∀ᵐ ω ∂planarBrownianMotion x, IsTimeChangeClock (G ω)) {u : ℝ≥0} (hu : 0 < u) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 ((x - a) / (L : ℂ)), 0 < A u b := by
  have hxK : x ∈ closedSquare a L := interior_subset hx
  have hx' : (x - a) / (L : ℂ) ∈ closedSquare 0 1 := by
    have h : x ∈ (fun z : ℂ => (z - a) / (L : ℂ)) ⁻¹' closedSquare 0 1 := by
      rw [unitSquareChart_preimage_closedSquare hL]
      exact hxK
    exact h
  have hfm := measurable_comp_squareFoldCM a L
  have hΨm : Measurable (unitSquarePathChart a hL) := (unitSquarePathChart a hL).continuous.measurable
  have hQ : reflectedPlanarBrownianMotion a L x =
      (planarBrownianMotion x).map fun ω => (squareFoldCM a L).comp ω :=
    Kernel.map_apply _ hfm x
  have hmap := reflectedPlanarBrownianMotion_map_unitSquarePathChart a hL x
  have hSm : MeasurableSet {b : ContinuousPath ℂ | 0 < A u b} :=
    measurableSet_lt measurable_const (hA.measurable u)
  -- facts along the planar path
  have h1 : ∀ᵐ ω ∂planarBrownianMotion x, ∀ s : ℝ≥0, F ((squareFoldCM a L).comp ω) s =
      M * (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL ((squareFoldCM a L).comp ω)) : ℝ) :=
    ae_of_ae_map hfm.aemeasurable (by rw [← hQ]; exact hFA)
  have h2 : ∀ᵐ ω ∂planarBrownianMotion x,
      Monotone fun t => A t (unitSquarePathChart a hL ((squareFoldCM a L).comp ω)) := by
    have h := hA.path _ hx'
    rw [← hmap] at h
    have h' := ae_of_ae_map hΨm.aemeasurable h
    rw [hQ] at h'
    filter_upwards [ae_of_ae_map hfm.aemeasurable h'] with ω hω using hω.2.2
  have h5 : ∀ᵐ ω ∂planarBrownianMotion x, ∀ n : ℕ,
      (∀ v ≤ 1 / ((n : ℝ≥0) + 1), ω v ∈ closedSquare a L) →
        ∀ t ≤ 1 / ((n : ℝ≥0) + 1), F ((squareFoldCM a L).comp ω) t = G ω t :=
    ae_all_iff.2 fun n => ae_isLQGClock_reflected_eq_planar hL hF hG _
  rw [← hmap]
  refine (ae_map_iff (p := fun b => 0 < A u b) hΨm.aemeasurable hSm).2 ?_
  rw [hQ]
  refine (ae_map_iff (p := fun b => 0 < A u (unitSquarePathChart a hL b)) hfm.aemeasurable
    (hΨm hSm)).2 ?_
  filter_upwards [h1, h2, hGs, ae_planarBrownianMotion_eval_zero x, h5] with ω e1 e2 e3 e4 e5
  -- the planar path stays in the square up to a positive time
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_interior.1 hx
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ≥0), ω t ∈ U := by
    have hc : Tendsto ω (𝓝 0) (𝓝 (ω 0)) := ω.continuous.continuousAt
    rw [e4] at hc
    exact hc (hUopen.mem_nhds hxU)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  set T : ℝ≥0 := 1 / ((n : ℝ≥0) + 1) with hT_def
  have hTr : (T : ℝ) = 1 / ((n : ℝ) + 1) := by simp [hT_def]
  have hT : ∀ v ≤ T, ω v ∈ closedSquare a L := by
    intro v hv
    refine hUsub (hball ?_)
    rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg v.coe_nonneg]
    have hv' : (v : ℝ) ≤ T := by exact_mod_cast hv
    linarith
  have hFG := e5 n hT
  have hL2 : 0 < (L ^ 2).toNNReal := Real.toNNReal_pos.2 (by positivity)
  set s : ℝ≥0 := min T (u * (L ^ 2).toNNReal) with hs_def
  have hs0 : 0 < s := lt_min (by rw [hT_def]; positivity) (mul_pos hu hL2)
  have hGpos : 0 < G ω s := by
    have h := e3.strictMono hs0
    rwa [e3.map_zero] at h
  have hApos : 0 < A (s / (L ^ 2).toNNReal)
      (unitSquarePathChart a hL ((squareFoldCM a L).comp ω)) := by
    have h := e1 s
    rw [hFG s (min_le_left _ _)] at h
    rw [h] at hGpos
    exact_mod_cast pos_of_mul_pos_right hGpos hM.le
  have hsu : s / (L ^ 2).toNNReal ≤ u := by
    rw [div_le_iff₀ hL2]
    exact min_le_right _ _
  exact hApos.trans_le (e2 hsu)

/-- **The unit-square clock is positive at positive times from almost every start.** If the
frontier of `K = closedSquare a L` is `m`-null, then for almost every start for the normalized
measure `unitSquareNormalizedMeasure m a L`, almost surely `0 < A u` for every `u > 0`. -/
theorem ae_ae_forall_pos_unitSquareClock {γ : ℝ} {hε : ℝ → ℂ → ℝ} {a : ℂ} {L : ℝ}
    (hL : 0 < L) {M : ℝ} (hM : 0 < M) {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {m : Measure ℂ} (hm : m (frontier (closedSquare a L)) = 0)
    {F G : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ}
    (hF : ∀ x ∈ closedSquare a L, IsLQGClock (reflectedPlanarBrownianMotion a L) γ hε x (F x))
    (hFA : ∀ x ∈ closedSquare a L, ∀ᵐ b ∂reflectedPlanarBrownianMotion a L x, ∀ s : ℝ≥0,
      F x b s = M * (A (s / (L ^ 2).toNNReal) (unitSquarePathChart a hL b) : ℝ))
    (hG : ∀ x, IsLQGClock planarBrownianMotion γ hε x (G x))
    (hGs : ∀ x, ∀ᵐ ω ∂planarBrownianMotion x, IsTimeChangeClock (G x ω)) :
    ∀ᵐ x' ∂unitSquareNormalizedMeasure m a L,
      ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x', ∀ u : ℝ≥0, 0 < u → 0 < A u b := by
  set K := closedSquare a L with hK
  have hKm : MeasurableSet K := (isCompact_closedSquare a L).isClosed.measurableSet
  have hL0 : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hL.ne'
  have hchart : ∀ z : ℂ, a + (L : ℂ) * ((z - a) / (L : ℂ)) = z := fun z => by
    field_simp
    ring
  have hint : ∀ᵐ x' ∂unitSquareNormalizedMeasure m a L, a + (L : ℂ) * x' ∈ interior K := by
    have hopen : MeasurableSet {x' : ℂ | a + (L : ℂ) * x' ∈ interior K} :=
      (isOpen_interior.preimage (by fun_prop : Continuous fun x' : ℂ => a + (L : ℂ) * x')).measurableSet
    unfold unitSquareNormalizedMeasure
    refine Measure.ae_smul_measure ?_ _
    refine (ae_map_iff (measurable_unitSquareChart a L).aemeasurable hopen).2 ?_
    rw [ae_restrict_iff' hKm]
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_) hm
    simp only [mem_ofPred_eq, not_imp, hchart] at hz
    exact (show z ∈ closure K \ interior K from ⟨subset_closure hz.1, hz.2⟩)
  filter_upwards [hint] with x' hx'
  have hxK : a + (L : ℂ) * x' ∈ K := interior_subset hx'
  have hx'K : x' ∈ closedSquare 0 1 := by
    have h : a + (L : ℂ) * x' ∈ (fun z : ℂ => (z - a) / (L : ℂ)) ⁻¹' closedSquare 0 1 := by
      rw [unitSquareChart_preimage_closedSquare hL]
      exact hxK
    have he : (a + (L : ℂ) * x' - a) / (L : ℂ) = x' := by
      field_simp
      ring
    simpa only [mem_preimage, he] using h
  have he : (a + (L : ℂ) * x' - a) / (L : ℂ) = x' := by
    field_simp
    ring
  have hn : ∀ n : ℕ, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 x',
      0 < A (1 / ((n : ℝ≥0) + 1)) b := by
    intro n
    have h := ae_pos_unitSquareClock_of_mem_interior hL hM hA hx' (hF _ hxK) (hFA _ hxK)
      (hG _) (hGs _) (u := 1 / ((n : ℝ≥0) + 1)) (by positivity)
    rwa [he] at h
  filter_upwards [ae_all_iff.2 hn, hA.path x' hx'K] with b hb hpath u hu
  obtain ⟨n, hn'⟩ := exists_nat_one_div_lt hu
  exact (hb n).trans_le (hpath.2.2 hn'.le)

end HarmonicBalls
