import HarmonicBalls.Proofs.Potential.LBMClauseEveryStartClock
import HarmonicBalls.Proofs.Potential.WeightedPrimitiveCauchy
import HarmonicBalls.Proofs.Sec6.LogAnnulusHitting

/-!
# LQG clocks of the inserted field from every start, for every `0 < γ < 2`

For the field `h^α = h - α log |·|`, the circle averages are `h^α_ε(z) = h_ε(z) - α log max(ε, |z|)`
(`fieldCircleAverage_eq`). Along a Brownian path `b` started at `1`, which almost surely never
visits `0` (`Section6.planarBrownianMotion_point_avoidance`), `|b_s|` is bounded below by some
`δ > 0` on `[0, T]`. For `ε_k ≤ δ` the approximate clock of `h^α` is the approximate clock of `h`
weighted by the continuous function `s ↦ |b_s|^{-γα}`:
`A^α_k(t) = ∫_0^t |b_s|^{-γα} dA^0_k(s)`. The approximate clocks of `h` converge almost surely
locally uniformly (`ae_exists_locally_uniform_limit_clock_zero`, every `0 < γ < 2`), so the weighted
ones are uniformly Cauchy on `[0, T]` (`weightedPrimitive_uniformCauchy`). Hence the approximate
clocks of `h^α` from the start `1` are almost surely Cauchy in probability, and
`ae_forall_exists_isLQGClock_of_cauchy` gives an LQG clock of `h^α` from every start.

This removes the restriction `γ² < 2` of `exists_ae_forall_isLQGClock_of_sq_lt_two` and the
restriction of sample spaces to `Type`: `exists_ae_forall_isLQGClock` holds for every
`0 < γ < 2`, every `α < Q` and every sample space, and `exists_lbmClause` is the LBM clause of
Proposition 2.5 for a family of clocks that exists.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric MarkovProcess
open scoped ENNReal NNReal

/-- **The approximate clocks of the inserted field along a path avoiding the insertion point are
uniformly Cauchy** on bounded time sets, if those of the field without insertion converge locally
uniformly. -/
theorem uniformCauchy_inserted_of_zero {γ α : ℝ} {hcirc : ℝ → ℂ → ℝ}
    (hc0 : ∀ k, Continuous (fieldCircleAverage 0 hcirc (dyadicScale k))) {b : ContinuousPath ℂ}
    (hb : ∀ t, b t ≠ 0)
    (hconv : ∃ F : ℝ≥0 → ℝ, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
      ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ T →
        |lqgClockApprox γ (fieldCircleAverage 0 hcirc) (dyadicScale (n + 1)) b t - F t| < η)
    (T : ℝ≥0) {η : ℝ} (hη : 0 < η) : ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k → ∀ t ≤ T,
      |lqgClockApprox γ (fieldCircleAverage α hcirc) (dyadicScale j) b t -
        lqgClockApprox γ (fieldCircleAverage α hcirc) (dyadicScale k) b t| < η := by
  -- the distance of the path to the insertion point on `[0, T]`
  have hcb : Continuous fun s : ℝ => ‖b s.toNNReal‖ :=
    continuous_norm.comp (b.continuous.comp continuous_real_toNNReal)
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (NNReal.coe_nonneg T))
    hcb.continuousOn
  set δ : ℝ := ‖b s₀.toNNReal‖ with hδ
  have hδpos : 0 < δ := norm_pos_iff.2 (hb _)
  have hδle : ∀ s ∈ Icc (0 : ℝ) T, δ ≤ ‖b s.toNNReal‖ := fun s hs => hmin hs
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδpos (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hscale : ∀ k, K ≤ k → dyadicScale k ≤ δ := fun k hk =>
    le_trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk) hK.le
  -- the weight and the densities without insertion
  set g : ℝ → ℝ := fun s => Real.exp (-(γ * α) * Real.log ‖b s.toNNReal‖) with hg
  have hgc : Continuous g := by
    refine Real.continuous_exp.comp (continuous_const.mul ?_)
    refine continuous_iff_continuousAt.2 fun s => ?_
    exact ContinuousAt.comp (g := Real.log) (f := fun s : ℝ => ‖b s.toNNReal‖) (x := s)
      (Real.continuousAt_log (norm_ne_zero_iff.2 (hb _))) hcb.continuousAt
  set f : ℕ → ℝ → ℝ := fun k s => dyadicScale k ^ (γ ^ 2 / 2) *
    Real.exp (γ * fieldCircleAverage 0 hcirc (dyadicScale k) (b s.toNNReal)) with hf
  have hfc : ∀ k, Continuous (f k) := fun k =>
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      ((hc0 k).comp (b.continuous.comp continuous_real_toNNReal))))
  have hf0 : ∀ k s, 0 ≤ f k s := fun k s =>
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
  -- for small scales the inserted density is the weighted density
  have hdens : ∀ k, K ≤ k → ∀ s ∈ Icc (0 : ℝ) T,
      dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α hcirc (dyadicScale k)
        (b s.toNNReal)) = g s * f k s := by
    intro k hk s hs
    have hmax : max (dyadicScale k) ‖b s.toNNReal‖ = ‖b s.toNNReal‖ :=
      max_eq_right ((hscale k hk).trans (hδle s hs))
    simp only [hg, hf, fieldCircleAverage_eq _ _ (dyadicScale_pos k), hmax, zero_mul, sub_zero]
    rw [mul_left_comm, ← Real.exp_add]
    congr 2
    ring
  have hA : ∀ k, K ≤ k → ∀ t : ℝ≥0, t ≤ T →
      lqgClockApprox γ (fieldCircleAverage α hcirc) (dyadicScale k) b t =
        ∫ s in (0 : ℝ)..(t : ℝ), g s * f k s := by
    intro k hk t htT
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
    exact hdens k hk s ⟨hs.1, hs.2.trans (by exact_mod_cast htT)⟩
  -- the primitives without insertion are uniformly Cauchy and bounded
  have hF : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ j, N ≤ j → ∀ k, N ≤ k → ∀ t ∈ Icc (0 : ℝ) T,
      |(∫ s in (0 : ℝ)..t, f j s) - ∫ s in (0 : ℝ)..t, f k s| ≤ ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := uniformCauchy_of_exists_locally_uniform hconv T hε
    refine ⟨N, fun j hj k hk t ht => ?_⟩
    have h := hN j hj k hk t.toNNReal (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht.1]; exact ht.2)
    have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal _ ht.1
    simp only [lqgClockApprox, hcoe] at h
    exact h.le
  have hB : ∃ B : ℝ, ∀ k, (∫ s in (0 : ℝ)..(T : ℝ), f k s) ≤ B := by
    obtain ⟨N, hN⟩ := uniformCauchy_of_exists_locally_uniform hconv T one_pos
    refine ⟨(∑ k ∈ Finset.range (N + 1), ∫ s in (0 : ℝ)..(T : ℝ), f k s) + 1, fun k => ?_⟩
    have hnn : ∀ i, 0 ≤ ∫ s in (0 : ℝ)..(T : ℝ), f i s := fun i =>
      intervalIntegral.integral_nonneg (NNReal.coe_nonneg T) fun s _ => hf0 i s
    rcases lt_or_ge k (N + 1) with hk | hk
    · have := Finset.single_le_sum (f := fun i => ∫ s in (0 : ℝ)..(T : ℝ), f i s)
        (fun i _ => hnn i) (Finset.mem_range.2 hk)
      linarith
    · have h := hN k (by omega) N le_rfl T le_rfl
      have hle := Finset.single_le_sum (f := fun i => ∫ s in (0 : ℝ)..(T : ℝ), f i s)
        (fun i _ => hnn i) (Finset.mem_range.2 (Nat.lt_succ_self N))
      have h' : (∫ s in (0 : ℝ)..(T : ℝ), f k s) - ∫ s in (0 : ℝ)..(T : ℝ), f N s < 1 := by
        refine (le_abs_self _).trans_lt ?_
        simpa only [lqgClockApprox] using h
      linarith
  obtain ⟨N, hN⟩ := weightedPrimitive_uniformCauchy (NNReal.coe_nonneg T) hgc.continuousOn hfc hf0
    hF hB (η / 2) (by positivity)
  refine ⟨max N K, fun j hj k hk t htT => ?_⟩
  rw [hA j (le_of_max_le_right hj) t htT, hA k (le_of_max_le_right hk) t htT]
  exact (hN j (le_of_max_le_left hj) k (le_of_max_le_left hk) t
    ⟨NNReal.coe_nonneg t, by exact_mod_cast htT⟩).trans_lt (by linarith)

/-- **The approximate clocks of the inserted field are almost surely Cauchy in probability from the
start `1`**, for every `0 < γ < 2` and every `α`. -/
theorem ae_cauchy_inserted_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ θ : ℝ, 0 < θ → ∃ N : ℕ, ∀ j, N ≤ j →
      ∀ k, N ≤ k → planarBrownianMotion 1 {b | ∃ t ≤ T, η ≤
        |lqgClockApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale j) b t -
          lqgClockApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) b t|} ≤
        ENNReal.ofReal θ := by
  have hLP := (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hloc := Measure.ae_ae_of_ae_prod (ae_exists_locally_uniform_limit_clock_zero hLP hγ hγ2 1)
  filter_upwards [hloc, ae_continuous_fieldCircleAverage hLP α, ae_continuous_fieldCircleAverage hLP 0]
    with ω hω hcα hc0 T η hη θ hθ
  refine cauchy_of_ae_uniformCauchy (fun k => hcα _ (dyadicScale_pos k)) ?_ T hη hθ
  filter_upwards [hω, Section6.planarBrownianMotion_point_avoidance 1 0 one_ne_zero] with b hb hb0
  intro T' η' hη'
  obtain ⟨F, -, -, -, hF⟩ := hb
  exact uniformCauchy_inserted_of_zero (fun k => hc0 _ (dyadicScale_pos k)) hb0 ⟨F, hF⟩ T' hη'

/-- **A version of the LQG clock of the inserted field from every start**: for a whole-plane GFF on
any sample space, every `0 < γ < 2` and every `α < Q`, there is a family `F` such that, for almost
every field, `F ω x` is an LQG clock of the inserted field from every start `x`. -/
theorem exists_ae_forall_isLQGClock {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ, ∀ᵐ ω ∂P, ∀ x : ℂ,
      IsLQGClock planarBrownianMotion γ (fieldCircleAverage α (hcirc ω)) x (F ω x) := by
  have hall := ae_forall_exists_isLQGClock_of_cauchy hh hγ hγ2 hα (x₀ := 1)
    (ae_cauchy_inserted_one hh hγ hγ2 α)
  exact ⟨fun ω x => Classical.epsilon fun F => IsLQGClock planarBrownianMotion γ
    (fieldCircleAverage α (hcirc ω)) x F, hall.mono fun ω hω x => Classical.epsilon_spec (hω x)⟩

/-- **Proposition 2.5, LBM clause, with its clock**: for a whole-plane GFF on any sample space,
every `0 < γ < 2` and every `α₀ < Q`, there is a family of LQG clocks of the inserted field from
every start, and for it, almost surely, the expected exit time of Liouville Brownian motion from
every smooth bounded open set is finite and Hölder continuous in the start. -/
theorem exists_lbmClause {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ F : Ω → ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ,
      (∀ᵐ ω ∂P, ∀ x : ℂ, IsLQGClock planarBrownianMotion γ (fieldCircleAverage α₀ (hcirc ω)) x (F ω x)) ∧
      ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O →
        (∀ x ∈ O, expectedLBMExitTime (F ω x) O x < ⊤) ∧
          ∃ C r : ℝ≥0, 0 < r ∧
            HolderOnWith C r (fun x => (expectedLBMExitTime (F ω x) O x).toReal) O := by
  obtain ⟨F, hF⟩ := exists_ae_forall_isLQGClock hh hγ hγ2 hα
  exact ⟨F, hF, greenPotentialLiouvilleHolder_lbmClause_of_lt_two hγ hγ2 hα hh hμ F hF⟩

end HarmonicBalls
