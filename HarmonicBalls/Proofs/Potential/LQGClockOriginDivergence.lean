import HarmonicBalls.Proofs.Potential.LQGClockScalingDivergence
import HarmonicBalls.Proofs.Potential.LQGClockScalingPrefactor

/-! # Divergence of the LQG clock from the origin by scaling

Bertacco and Gwynne (arXiv:2501.15936v2), proof of Theorem 5.12 (B4), for the LQG clock of the
inserted field `h = h^ℂ - α log |·|` of planar Brownian motion from the origin, with the
deterministic times `4^m` in place of the exit times of the balls `B(0, 2^m)`. For `m ≥ 0` let
`F'_m` be an LQG clock from the origin of the field rescaled by `2^m` (`rescaledCircleAverage`),
and let `Y_m = F'_m(b̃_m)(1)` with the rescaled path `b̃_m(u) = 2^{-m} b(4^m u)`. Almost surely
`F(4^m) = c_m Y_m` with `c_m = 2^{m (2 + γ²/2 - γ α)} e^{γ h_{2^m}(0)}`
(`ae_lqgClock_mul_time_eq`), and `c_m → ∞` almost surely since `2 + γ²/2 - γ α = γ (Q - α) > 0`
(`ae_tendsto_rpow_mul_exp_circle_atTop`). If the `Y_m` are identically distributed under the
joint law of the field and the path (the rescaled field is again a whole-plane GFF and the
rescaled path is again a planar Brownian motion from the origin) and `Y_0` is almost surely
positive, the clock tends to infinity, for almost every field and almost every path.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- The deduction of `ae_tendsto_atTop_of_le_mul_of_map_eq` without the monotonicity hypothesis:
almost surely, if the clock is nondecreasing then it tends to infinity. -/
theorem ae_monotone_imp_tendsto_atTop_of_le_mul_of_map_eq {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] (F : X → ℝ≥0 → ℝ) (τ : ℕ → X → ℝ≥0)
    (c Y : ℕ → X → ℝ) (hscale : ∀ n, ∀ᵐ p ∂μ, c n p * Y n p ≤ F p (τ n p))
    (hc : ∀ᵐ p ∂μ, Tendsto (fun n => c n p) atTop atTop)
    (hYm : ∀ n, Measurable (Y n)) (hlaw : ∀ n, μ.map (Y n) = μ.map (Y 0))
    (hpos : ∀ᵐ p ∂μ, 0 < Y 0 p) :
    ∀ᵐ p ∂μ, Monotone (F p) → Tendsto (F p) atTop atTop := by
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hδ (k : ℕ) : 0 < δ k := by positivity
  have hlawδ (k n : ℕ) : μ {p | δ k ≤ Y n p} = μ {p | δ k ≤ Y 0 p} := by
    have h1 := Measure.map_apply (μ := μ) (hYm n) (measurableSet_Ici (a := δ k))
    have h2 := Measure.map_apply (μ := μ) (hYm 0) (measurableSet_Ici (a := δ k))
    rw [hlaw n] at h1
    exact h1.symm.trans h2
  let U : ℕ → ℕ → Set X := fun k n => ⋃ j : ℕ, {p | δ k ≤ Y (n + j) p}
  let L : ℕ → Set X := fun k => ⋂ n : ℕ, U k n
  have hUm (k n : ℕ) : MeasurableSet (U k n) :=
    MeasurableSet.iUnion fun j => measurableSet_le measurable_const (hYm (n + j))
  have hLm (k : ℕ) : MeasurableSet (L k) := MeasurableSet.iInter fun n => hUm k n
  have hUanti (k : ℕ) : Antitone (U k) := by
    intro n n' hnn' p hp
    simp only [U, mem_iUnion, mem_ofPred_eq] at hp ⊢
    obtain ⟨j, hj⟩ := hp
    refine ⟨n' - n + j, ?_⟩
    have : n + (n' - n + j) = n' + j := by omega
    rw [this]
    exact hj
  have hLge (k : ℕ) : μ {p | δ k ≤ Y 0 p} ≤ μ (L k) := by
    have ht := tendsto_measure_iInter_atTop (μ := μ) (fun n => (hUm k n).nullMeasurableSet)
      (hUanti k) ⟨0, measure_ne_top μ _⟩
    refine ge_of_tendsto' ht fun n => ?_
    rw [← hlawδ k n]
    refine measure_mono fun p hp => ?_
    simp only [U, mem_iUnion]
    exact ⟨0, by simpa using hp⟩
  have hgood : ∀ᵐ p ∂μ, Tendsto (fun n => c n p) atTop atTop ∧
      ∀ n, c n p * Y n p ≤ F p (τ n p) := by
    filter_upwards [hc, ae_all_iff.mpr hscale] with p h2 h3
    exact ⟨h2, h3⟩
  obtain ⟨E, hEnull, hE⟩ : ∃ E : Set X, μ E = 0 ∧ ∀ p ∉ E,
      Tendsto (fun n => c n p) atTop atTop ∧ ∀ n, c n p * Y n p ≤ F p (τ n p) :=
    ⟨_, ae_iff.mp hgood, fun p hp => by simpa using hp⟩
  have hbound (k : ℕ) : μ {p | ¬ (Monotone (F p) → Tendsto (F p) atTop atTop)} ≤
      μ {p | Y 0 p < δ k} := by
    have hsub : {p | ¬ (Monotone (F p) → Tendsto (F p) atTop atTop)} ⊆ (L k)ᶜ ∪ E := by
      intro p hp
      simp only [mem_ofPred_eq, Classical.not_imp] at hp
      obtain ⟨hm, hp⟩ := hp
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      obtain ⟨hpL, hpE⟩ := hcon
      obtain ⟨hcp, hs⟩ := hE p hpE
      refine hp (tendsto_atTop_of_frequently_le_mul hm hs hcp (hδ k) fun N => ?_)
      have hpU : p ∈ U k N := mem_iInter.mp hpL N
      simp only [U, mem_iUnion, mem_ofPred_eq] at hpU
      obtain ⟨j, hj⟩ := hpU
      exact ⟨N + j, Nat.le_add_right N j, hj⟩
    have hYlt : {p | Y 0 p < δ k} = {p | δ k ≤ Y 0 p}ᶜ := by
      ext p
      simp [not_le]
    calc μ {p | ¬ (Monotone (F p) → Tendsto (F p) atTop atTop)} ≤ μ ((L k)ᶜ ∪ E) :=
          measure_mono hsub
      _ ≤ μ (L k)ᶜ + μ E := measure_union_le _ _
      _ = μ (L k)ᶜ := by rw [hEnull, add_zero]
      _ = 1 - μ (L k) := prob_compl_eq_one_sub (hLm k)
      _ ≤ 1 - μ {p | δ k ≤ Y 0 p} := tsub_le_tsub_left (hLge k) 1
      _ = μ {p | Y 0 p < δ k} := by
        rw [hYlt, prob_compl_eq_one_sub (measurableSet_le measurable_const (hYm 0))]
  have hlim : Tendsto (fun k => μ {p | Y 0 p < δ k}) atTop (𝓝 0) := by
    have hanti : Antitone fun k => {p | Y 0 p < δ k} := by
      intro k k' hkk' p hp
      simp only [mem_ofPred_eq] at hp ⊢
      refine lt_of_lt_of_le hp ?_
      simp only [δ]
      gcongr
    have ht := tendsto_measure_iInter_atTop (μ := μ)
      (fun k => (measurableSet_lt (hYm 0) measurable_const).nullMeasurableSet) hanti
      ⟨0, measure_ne_top μ _⟩
    have hinter : μ (⋂ k, {p | Y 0 p < δ k}) = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hpos)
      intro p hp
      simp only [mem_iInter, mem_ofPred_eq] at hp
      simp only [mem_ofPred_eq, not_lt]
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
      have := hp k
      simp only [δ] at this
      linarith
    rw [hinter] at ht
    exact ht
  have h0 : μ {p | ¬ (Monotone (F p) → Tendsto (F p) atTop atTop)} = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  exact ae_iff.mpr h0

/-- Bertacco-Gwynne 2025, Theorem 5.12 (B4), for the LQG clock of the inserted field from the
origin, with deterministic times `4^m`: if `F` is a jointly measurable LQG clock from the origin,
`F' m` are LQG clocks from the origin of the fields rescaled by `2^m`, the rescaled clocks
`Y_m = F' m ω (b̃_m) 1` along the rescaled paths are jointly measurable and identically distributed
under the product of the field law and the Brownian law, and `Y_0` is almost surely positive, then
for almost every field the clock tends to infinity for almost every path. -/
theorem ae_ae_tendsto_atTop_of_rescaled_clocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α : ℝ} (hγ : 0 < γ)
    (hα : α < lqgQ γ) (F : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF : ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (hcirc ω)) 0 (F ω))
    (hFm : ∀ t : ℝ≥0, Measurable fun p : Ω × ContinuousPath ℂ => F p.1 p.2 t)
    (F' : ℕ → Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (hF' : ∀ m : ℕ, ∀ᵐ ω ∂P, IsLQGClock planarBrownianMotion γ
      (LatticeProb.Gauss.fieldCircleAverage α (rescaledCircleAverage (hcirc ω) ((2 : ℝ) ^ m)))
        0 (F' m ω))
    (hYm : ∀ m : ℕ, Measurable fun p : Ω × ContinuousPath ℂ =>
      F' m p.1 (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal p.2) 1)
    (hlaw : ∀ m : ℕ, (P.prod (planarBrownianMotion 0)).map (fun p =>
        F' m p.1 (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal p.2) 1) =
      (P.prod (planarBrownianMotion 0)).map (fun p =>
        F' 0 p.1 (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ 0) ^ 2).toNNReal p.2) 1))
    (hpos : ∀ᵐ p ∂(P.prod (planarBrownianMotion 0)),
      0 < F' 0 p.1 (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ 0) ^ 2).toNNReal p.2) 1) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion 0), Tendsto (F ω b) atTop atTop := by
  have hP := hh.isProbabilityMeasure
  set a : ℝ := 2 + γ ^ 2 / 2 - γ * α with hadef
  have ha : 0 < a := by
    have hγ0 : γ ≠ 0 := hγ.ne'
    have hQ : γ * lqgQ γ = 2 + γ ^ 2 / 2 := by
      rw [lqgQ]
      field_simp
    have : 0 < γ * (lqgQ γ - α) := mul_pos hγ (by linarith)
    rw [hadef]
    nlinarith
  let c : ℕ → Ω × ContinuousPath ℂ → ℝ := fun m p =>
    ((2 : ℝ) ^ m) ^ a * Real.exp (γ * hcirc p.1 ((2 : ℝ) ^ m) 0)
  let Y : ℕ → Ω × ContinuousPath ℂ → ℝ := fun m p =>
    F' m p.1 (Section6.scaledCenteredPlanarPath 0 (((2 : ℝ) ^ m) ^ 2).toNNReal p.2) 1
  let τ : ℕ → Ω × ContinuousPath ℂ → ℝ≥0 := fun m _ => (((2 : ℝ) ^ m) ^ 2).toNNReal * 1
  have hcm (m : ℕ) : Measurable (c m) :=
    measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
      ((hh.measurable_circle ((2 : ℝ) ^ m) 0 (by positivity)).comp measurable_fst)))
  have hscale (m : ℕ) : ∀ᵐ p ∂(P.prod (planarBrownianMotion 0)),
      c m p * Y m p ≤ F p.1 p.2 (τ m p) := by
    have hS : MeasurableSet {p : Ω × ContinuousPath ℂ | c m p * Y m p ≤ F p.1 p.2 (τ m p)} :=
      measurableSet_le ((hcm m).mul (hYm m)) (hFm _)
    refine (Measure.ae_prod_iff_ae_ae hS).mpr ?_
    filter_upwards [hF, hF' m] with ω hω hω'
    filter_upwards [ae_lqgClock_mul_time_eq m hω hω'] with b hb
    exact le_of_eq (hb 1).symm
  have hc0 := ae_tendsto_rpow_mul_exp_circle_atTop hh γ ha
  have hc : ∀ᵐ p ∂(P.prod (planarBrownianMotion 0)), Tendsto (fun m => c m p) atTop atTop := by
    have h := Measure.QuasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion 0)) hc0
    filter_upwards [h] with p hp
    exact hp
  have hmain := ae_monotone_imp_tendsto_atTop_of_le_mul_of_map_eq
    (μ := P.prod (planarBrownianMotion 0))
    (fun p => F p.1 p.2) τ c Y hscale hc hYm hlaw hpos
  have hmono : ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion 0), Monotone (F ω b) := by
    filter_upwards [hF, ae_continuous_fieldCircleAverage hh α] with ω hω hcω
    filter_upwards [ae_zero_continuous_monotone_of_isLQGClock
      (fun k => hcω _ (dyadicScale_pos k)) hω] with b hb
    exact hb.2.2
  filter_upwards [Measure.ae_ae_of_ae_prod hmain, hmono] with ω h1 h2
  filter_upwards [h1, h2] with b hb1 hb2
  exact hb1 hb2

end HarmonicBalls
