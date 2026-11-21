import HarmonicBalls.Proofs.Potential.LQGClockExteriorExhaustion
import HarmonicBalls.Proofs.Sec6.LogAnnulusHitting

/-! # Half-disc clocks from starts away from the insertion

Planar Brownian motion started away from the insertion point almost surely never visits it,
so on every bounded time interval its path stays outside a small disc around the insertion.
On such an interval the half-disc clocks coincide with annular clocks, whose dyadic
approximations converge locally uniformly for `γ ^ 2 < 2` and every insertion. Hence the
half-disc clocks converge locally uniformly, with a jointly measurable limit, for every
insertion `α`, and with limits of the exterior clocks the inserted field has an LQG clock from
every start other than the insertion point.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- From a start other than the insertion point, the dyadic half-disc clocks converge locally
uniformly in time for every insertion, when `γ ^ 2 < 2`. -/
theorem ae_exists_locally_uniform_limit_halfDiscClock_of_ne_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {x : ℂ} (hx : x ≠ 0) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) :
    ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F t| < η := by
  let δ : ℕ → ℝ := fun n => (2 : ℝ)⁻¹ ^ (n+2)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hann : ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)), ∀ n : ℕ,
      ∃ F : ℝ≥0 → ℝ, Continuous F ∧ (∀ t, 0 ≤ F t) ∧ Monotone F ∧
        ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | δ n ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale j)^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale j) z))
                  (p.2 s.toNNReal)) - F t| < η :=
    ae_all_iff.mpr fun n => ae_exists_locally_uniform_limit_annularClock hh x hγ hγ2 α (hδ n)
  have havoid : ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∀ t : ℝ≥0, p.2 t ≠ 0 :=
    (Measure.quasiMeasurePreserving_snd (μ := P) (ν := planarBrownianMotion x)).ae
      (Section6.planarBrownianMotion_point_avoidance x 0 hx)
  filter_upwards [hann, havoid, (Measure.quasiMeasurePreserving_fst (μ := P)
    (ν := planarBrownianMotion x)).ae (ae_continuous_fieldCircleAverage hh α)] with p hp hav hc
  let f : ℕ → ℂ → ℝ := fun j z => (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z)
  have hfc (j : ℕ) : Continuous (f j) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hc _ (dyadicScale_pos _))))
  have hf0 (j : ℕ) (z : ℂ) : 0 ≤ f j z :=
    mul_nonneg (Real.rpow_nonneg (dyadicScale_pos _).le _) (Real.exp_pos _).le
  let B : Set ℂ := {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hB : MeasurableSet B := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let A : ℕ → ℝ≥0 → ℝ := fun j t => ∫ s in (0 : ℝ)..(t : ℝ), B.indicator (f j) (p.2 s.toNNReal)
  have hpath : Continuous (fun s : ℝ => p.2 s.toNNReal) :=
    p.2.continuous.comp continuous_real_toNNReal
  have hint (j : ℕ) (u v : ℝ) :
      IntervalIntegrable (fun s : ℝ => B.indicator (f j) (p.2 s.toNNReal)) volume u v := by
    apply ((hfc j).comp hpath).intervalIntegrable u v |>.mono_fun
      (((hfc j).measurable.indicator hB).comp hpath.measurable).aestronglyMeasurable
    filter_upwards with s
    by_cases hs : p.2 s.toNNReal ∈ B
    · simp [Set.indicator_of_mem hs]
    · simp [Set.indicator_of_notMem hs]
  have hind0 (j : ℕ) (s : ℝ) : 0 ≤ B.indicator (f j) (p.2 s.toNNReal) := by
    by_cases hs : p.2 s.toNNReal ∈ B
    · rw [Set.indicator_of_mem hs]
      exact hf0 j _
    · rw [Set.indicator_of_notMem hs]
  have hAc (j : ℕ) : Continuous (A j) :=
    (intervalIntegral.continuous_primitive (hint j) 0).comp NNReal.continuous_coe
  have hA0 (j : ℕ) (t : ℝ≥0) : 0 ≤ A j t :=
    intervalIntegral.integral_nonneg (NNReal.coe_nonneg t) (fun s _ => hind0 j s)
  have hAm (j : ℕ) : Monotone (A j) := by
    intro s t hst
    have hst' : (s : ℝ) ≤ t := hst
    have h := intervalIntegral.integral_add_adjacent_intervals (hint j 0 s) (hint j s t)
    have h2 : 0 ≤ ∫ u in (s : ℝ)..(t : ℝ), B.indicator (f j) (p.2 u.toNNReal) :=
      intervalIntegral.integral_nonneg hst' (fun u _ => hind0 j u)
    change (∫ u in (0 : ℝ)..(s : ℝ), B.indicator (f j) (p.2 u.toNNReal)) ≤
      ∫ u in (0 : ℝ)..(t : ℝ), B.indicator (f j) (p.2 u.toNNReal)
    linarith
  obtain ⟨F, hFc, hF0, hFm, hF⟩ :=
    exists_continuous_monotone_limit_of_uniform_on_nat_intervals A hAc hA0 hAm (by
      intro N
      have hK : IsCompact (Icc (0 : ℝ≥0) (N : ℝ≥0)) := isCompact_Icc
      obtain ⟨s₀, -, hmin⟩ := hK.exists_isMinOn (nonempty_Icc.mpr zero_le)
        (continuous_norm.comp p.2.continuous).continuousOn
      have hρ : 0 < ‖p.2 s₀‖ := norm_pos_iff.mpr (hav s₀)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hρ (by norm_num : (2 : ℝ)⁻¹ < 1)
      have hδn : δ n ≤ ‖p.2 s₀‖ := by
        have : δ n ≤ (2 : ℝ)⁻¹ ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        linarith
      obtain ⟨G, -, -, -, hG⟩ := hp n
      refine ⟨G, fun η hη => ?_⟩
      have hev := hG N η hη
      rw [eventually_atTop] at hev ⊢
      obtain ⟨J, hJ⟩ := hev
      refine ⟨J, fun j hj t ht => ?_⟩
      have h := hJ (j+1) (by omega) t ht
      have ht' : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast ht
      have heq : A j t = ∫ s in (0 : ℝ)..(t : ℝ),
          {z : ℂ | δ n ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                (p.2 s.toNNReal) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (NNReal.coe_nonneg t)] at hs
        have hsN : s.toNNReal ∈ Icc (0 : ℝ≥0) (N : ℝ≥0) :=
          ⟨zero_le, (Real.toNNReal_le_iff_le_coe).mpr (by exact_mod_cast hs.2.trans ht')⟩
        have hmin' : ‖p.2 s₀‖ ≤ ‖p.2 s.toNNReal‖ := hmin hsN
        have hge : δ n ≤ ‖p.2 s.toNNReal‖ := hδn.trans hmin'
        simp only
        by_cases h1 : ‖p.2 s.toNNReal‖ ≤ 1/2
        · rw [Set.indicator_of_mem (show p.2 s.toNNReal ∈ B from ⟨norm_nonneg _, h1⟩),
            Set.indicator_of_mem (show p.2 s.toNNReal ∈
              {z : ℂ | δ n ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from ⟨hge, h1⟩)]
        · rw [Set.indicator_of_notMem (show p.2 s.toNNReal ∉ B from fun h => h1 h.2),
            Set.indicator_of_notMem (show p.2 s.toNNReal ∉
              {z : ℂ | δ n ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2} from fun h => h1 h.2)]
      rw [heq]
      exact h)
  exact ⟨F, hFc, hF0, hFm, hF⟩
end HarmonicBalls
