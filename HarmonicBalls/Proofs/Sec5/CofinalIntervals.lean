import HarmonicBalls.Steps.Sec5.LocalIntervals

/-!
# Cofinal scaled intervals

The deterministic part of the cofinal-time argument in Theorem 5.5. It uses
neither monotonicity of scaled horizons nor independence between scales.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- If the scale factors diverge and the unscaled horizons exceed one positive
constant infinitely often, their products exceed every level infinitely often. -/
theorem frequently_lt_mul_of_tendsto_atTop {A T : ℕ → ℝ}
    (hA : Tendsto A atTop atTop) {c : ℝ} (hc : 0 < c)
    (hT : ∃ᶠ n in atTop, c < T n) (b : ℝ) :
    ∃ᶠ n in atTop, b < A n * T n := by
  have hlarge : ∀ᶠ n in atTop, max 0 (b / c) < A n :=
    hA.eventually (eventually_gt_atTop _)
  apply (hT.and_eventually hlarge).mono
  intro n hn
  have hApos : 0 < A n := lt_of_le_of_lt (le_max_left _ _) hn.2
  have hbound : b < A n * c := by
    have h := lt_of_le_of_lt (le_max_right 0 (b / c)) hn.2
    exact (div_lt_iff₀ hc).1 h
  exact lt_trans hbound (mul_lt_mul_of_pos_left hn.1 hApos)

/-- Scaling estimates on increasing ambient balls yield cofinal local
intervals at every centre. Only the radii tend to infinity: the horizons
need not increase. -/
theorem cofinal_local_intervals_of_frequently_scaled_horizons
    (μ : Measure ℂ) (R A T : ℕ → ℝ)
    (hR : Tendsto R atTop atTop) (hA : Tendsto A atTop atTop)
    (hpositive : ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, c < T n)
    (hloc : ∀ n z, z ∈ ball (0 : ℂ) (R n / 2) → 0 < A n * T n →
      SatisfiesHarmonicBallConditionsOn μ (regularizedCluster μ (R n) z) z (A n * T n) ∧
      ∀ t ∈ Ioo 0 (A n * T n), closure (cluster μ (R n) z t) ⊆ ball 0 (R n) ∧
        μ (frontier (cluster μ (R n) z t)) = 0) :
    ∀ z : ℂ, ∃ (r s : ℕ → ℝ),
      (∀ n, 0 < r n ∧ z ∈ ball 0 (r n) ∧ 0 < s n ∧
        SatisfiesHarmonicBallConditionsOn μ (regularizedCluster μ (r n) z) z (s n) ∧
        ∀ t ∈ Ioo 0 (s n), closure (cluster μ (r n) z t) ⊆ ball 0 (r n) ∧
          μ (frontier (cluster μ (r n) z t)) = 0) ∧
      (∀ t : ℝ, 0 < t → ∃ n, t < s n) := by
  intro z
  obtain ⟨c, hc, hT⟩ := hpositive
  have hz : ∀ᶠ n in atTop, z ∈ ball (0 : ℂ) (R n / 2) := by
    filter_upwards [hR.eventually (eventually_gt_atTop (2 * ‖z‖))] with n hn
    simp only [mem_ball, dist_zero_right]
    linarith
  have hex : ∀ m : ℕ, ∃ n, z ∈ ball (0 : ℂ) (R n / 2) ∧ (m : ℝ) + 1 < A n * T n := by
    intro m
    exact ((frequently_lt_mul_of_tendsto_atTop hA hc hT ((m : ℝ) + 1)).and_eventually hz).exists.imp
      (fun n hn => ⟨hn.2, hn.1⟩)
  choose k hk using hex
  refine ⟨fun n => R (k n), fun n => A (k n) * T (k n), ?_, ?_⟩
  · intro n
    have hzn := (hk n).1
    have hr : 0 < R (k n) := by
      simp only [mem_ball, dist_zero_right] at hzn
      have := norm_nonneg z
      linarith
    have hzn' : z ∈ ball (0 : ℂ) (R (k n)) :=
      (ball_subset_ball (by linarith : R (k n) / 2 ≤ R (k n))) hzn
    have ht : 0 < A (k n) * T (k n) := by
      have hm : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [(hk n).2]
    exact ⟨hr, hzn', ht, hloc (k n) z hzn ht⟩
  · intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact ⟨n, lt_trans hn (by linarith [(hk n).2])⟩

/-- Equal distributions and positivity give a positive lower bound along an
infinite subsequence almost surely. No independence is required. -/
theorem ae_frequently_gt_of_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℕ → Ω → ℝ)
    (hlaw : ∀ n, ProbabilityTheory.IdentDistrib (T n) (T 0) P P)
    (hpos : ∀ᵐ ω ∂P, 0 < T 0 ω) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, c < T n ω := by
  let S : ℕ → Set Ω := fun j => {ω | T 0 ω ≤ 1 / ((j : ℝ) + 1)}
  have hSm : ∀ j, NullMeasurableSet (S j) P := by
    intro j
    exact (hlaw 0).aemeasurable_fst.nullMeasurableSet_preimage measurableSet_Iic
  have hSa : Antitone S := by
    intro i j hij ω hω
    change T 0 ω ≤ 1 / ((j : ℝ) + 1) at hω
    change T 0 ω ≤ 1 / ((i : ℝ) + 1)
    apply hω.trans
    apply one_div_le_one_div_of_le (by positivity)
    have hcast : (i : ℝ) ≤ (j : ℝ) := Nat.cast_le.mpr hij
    linarith
  have hSint : P (⋂ j, S j) = 0 := by
    apply measure_mono_null _ (ae_iff.1 hpos)
    intro ω hω
    simp only [mem_iInter] at hω
    simp only [mem_ofPred_eq, not_lt]
    exact ge_of_tendsto
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0))
      (Eventually.of_forall hω)
  have hinf : (⨅ j, P (S j)) = 0 := by
    rw [← hSa.measure_iInter hSm ⟨0, measure_ne_top P _⟩]
    exact hSint
  let Bad : Set Ω := {ω | ¬ ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, c < T n ω}
  have hBad (j : ℕ) : P Bad ≤ P (S j) := by
    let E : ℕ → Set Ω := fun N => ⋂ n ≥ N, {ω | T n ω ≤ 1 / ((j : ℝ) + 1)}
    have hmono : Monotone E := by
      intro m n hmn ω hω
      simp only [E, mem_iInter, mem_ofPred_eq] at hω ⊢
      intro k hk
      exact hω k (hmn.trans hk)
    have hsubset : Bad ⊆ ⋃ N, E N := by
      intro ω hω
      have hn : ¬ ∃ᶠ n in atTop, 1 / ((j : ℝ) + 1) < T n ω := by
        intro hf
        exact hω ⟨_, by positivity, hf⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (not_frequently.1 hn)
      refine mem_iUnion.2 ⟨N, ?_⟩
      simp only [E, mem_iInter, mem_ofPred_eq]
      intro n hn
      exact le_of_not_gt (hN n hn)
    calc
      P Bad ≤ P (⋃ N, E N) := measure_mono hsubset
      _ = ⨆ N, P (E N) := hmono.measure_iUnion
      _ ≤ P (S j) := by
        refine iSup_le fun N => ?_
        have hsub : E N ⊆ {ω | T N ω ≤ 1 / ((j : ℝ) + 1)} := by
          intro ω hω
          simp only [E, mem_iInter, mem_ofPred_eq] at hω ⊢
          exact hω N le_rfl
        exact (measure_mono hsub).trans_eq ((hlaw N).measure_mem_eq measurableSet_Iic)
  have hzero : P Bad = 0 := by
    apply le_antisymm _ (zero_le)
    rw [← hinf]
    exact le_iInf hBad
  exact ae_iff.2 hzero

universe u

/-- The cofinal-interval step follows once scaled local estimates and the
positive frequently-occurring horizon have been established on one event. -/
theorem cofinalRegularizedClusterIntervals_of_scaledEstimates
    (hscaled : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ᵐ ω ∂P, ∃ (R A T : ℕ → ℝ), Tendsto R atTop atTop ∧
          Tendsto A atTop atTop ∧ (∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, c < T n) ∧
          ∀ n z, z ∈ ball (0 : ℂ) (R n / 2) → 0 < A n * T n →
            SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) (R n) z) z
              (A n * T n) ∧
            ∀ t ∈ Ioo 0 (A n * T n),
              closure (cluster (μ ω) (R n) z t) ⊆ ball 0 (R n) ∧
              μ ω (frontier (cluster (μ ω) (R n) z t)) = 0) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hscaled γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  obtain ⟨R, A, T, hR, hA, hT, hloc⟩ := hω
  exact cofinal_local_intervals_of_frequently_scaled_horizons (μ ω) R A T hR hA hT hloc

/-- A version of the cofinal-interval reduction in terms of identically
distributed positive horizons. The scale-transfer estimates and divergence
of the scale factors are explicit hypotheses. -/
theorem cofinalRegularizedClusterIntervals_of_identDistrib
    (hscaled : ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∃ (R A T : ℕ → Ω → ℝ),
          (∀ n, ProbabilityTheory.IdentDistrib (T n) (T 0) P P) ∧
          (∀ᵐ ω ∂P, 0 < T 0 ω) ∧
          ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop atTop ∧
            Tendsto (fun n => A n ω) atTop atTop ∧
            ∀ n z, z ∈ ball (0 : ℂ) (R n ω / 2) → 0 < A n ω * T n ω →
              SatisfiesHarmonicBallConditionsOn (μ ω)
                (regularizedCluster (μ ω) (R n ω) z) z (A n ω * T n ω) ∧
              ∀ t ∈ Ioo 0 (A n ω * T n ω),
                closure (cluster (μ ω) (R n ω) z t) ⊆ ball 0 (R n ω) ∧
                μ ω (frontier (cluster (μ ω) (R n ω) z t)) = 0) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨R, A, T, hlaw, hpos, hlocal⟩ :=
    hscaled γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  filter_upwards [hlocal, ae_frequently_gt_of_identDistrib P T hlaw hpos] with ω hω hT
  exact cofinal_local_intervals_of_frequently_scaled_horizons (μ ω)
    (fun n => R n ω) (fun n => A n ω) (fun n => T n ω) hω.1 hω.2.1 hT hω.2.2

end HarmonicBalls
