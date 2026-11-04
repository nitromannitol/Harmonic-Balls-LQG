import HarmonicBalls.Proofs.Sec5.CofinalIntervals

/-! # Frequently occurring events without measurability assumptions -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- If the outer probabilities of failure are uniformly bounded over the
scale index, and the bounds can be made arbitrarily small, then some event
in the family occurs infinitely often almost surely. The events themselves
need not be measurable, and independence is not required. -/
theorem ae_exists_frequently_of_uniform_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G : ℕ → ℕ → Set Ω) (b : ℕ → ℝ≥0∞)
    (hbound : ∀ m n, P (G m n)ᶜ ≤ b m) (hsmall : (⨅ m, b m) = 0) :
    ∀ᵐ ω ∂P, ∃ m, ∃ᶠ n in atTop, ω ∈ G m n := by
  let Bad : Set Ω := {ω | ¬ ∃ m, ∃ᶠ n in atTop, ω ∈ G m n}
  have hBad (m : ℕ) : P Bad ≤ b m := by
    let E : ℕ → Set Ω := fun N => ⋂ n ≥ N, (G m n)ᶜ
    have hmono : Monotone E := by
      intro i j hij ω hω
      simp only [E, mem_iInter, mem_compl_iff] at hω ⊢
      intro n hn
      exact hω n (hij.trans hn)
    have hsub : Bad ⊆ ⋃ N, E N := by
      intro ω hω
      have hn : ¬ ∃ᶠ n in atTop, ω ∈ G m n := fun hf => hω ⟨m, hf⟩
      obtain ⟨N, hN⟩ := eventually_atTop.1 (not_frequently.1 hn)
      refine mem_iUnion.2 ⟨N, ?_⟩
      simp only [E, mem_iInter, mem_compl_iff]
      exact hN
    calc
      P Bad ≤ P (⋃ N, E N) := measure_mono hsub
      _ = ⨆ N, P (E N) := hmono.measure_iUnion
      _ ≤ b m := by
        refine iSup_le fun N => ?_
        have hsub' : E N ⊆ (G m N)ᶜ := by
          intro ω hω
          simp only [E, mem_iInter, mem_compl_iff] at hω ⊢
          exact hω N le_rfl
        exact (measure_mono hsub').trans (hbound m N)
  have hzero : P Bad = 0 := by
    apply le_antisymm _ (zero_le)
    rw [← hsmall]
    exact le_iInf hBad
  exact ae_iff.2 hzero

/-- Uniform outer-probability estimates yield cofinal local cluster intervals
without requiring the scale events or their associated horizons to be
measurable. The local estimate is needed only on the corresponding good event. -/
theorem ae_cofinal_local_intervals_of_uniform_failure
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (R A : ℕ → Ω → ℝ) (s : ℕ → ℝ) (G : ℕ → ℕ → Set Ω) (b : ℕ → ℝ≥0∞)
    (hs : ∀ m, 0 < s m) (hbound : ∀ m n, P (G m n)ᶜ ≤ b m)
    (hsmall : (⨅ m, b m) = 0)
    (hscale : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop atTop ∧
      Tendsto (fun n => A n ω) atTop atTop)
    (hloc : ∀ᵐ ω ∂P, ∀ m n, ω ∈ G m n → ∀ z,
      z ∈ ball (0 : ℂ) (R n ω / 2) →
      SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) (R n ω) z) z
        (A n ω * s m) ∧
      ∀ t ∈ Ioo 0 (A n ω * s m),
        closure (cluster (μ ω) (R n ω) z t) ⊆ ball 0 (R n ω) ∧
        μ ω (frontier (cluster (μ ω) (R n ω) z t)) = 0) :
    ∀ᵐ ω ∂P, ∀ z : ℂ, ∃ (r t : ℕ → ℝ),
      (∀ n, 0 < r n ∧ z ∈ ball 0 (r n) ∧ 0 < t n ∧
        SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) (r n) z) z (t n) ∧
        ∀ q ∈ Ioo 0 (t n), closure (cluster (μ ω) (r n) z q) ⊆ ball 0 (r n) ∧
          μ ω (frontier (cluster (μ ω) (r n) z q)) = 0) ∧
      (∀ q : ℝ, 0 < q → ∃ n, q < t n) := by
  classical
  filter_upwards [ae_exists_frequently_of_uniform_failure P G b hbound hsmall,
    hscale, hloc] with ω hfreq hscale hloc
  obtain ⟨m, hm⟩ := hfreq
  let T : ℕ → ℝ := fun n => if ω ∈ G m n then s m else 0
  have hT : ∃ c : ℝ, 0 < c ∧ ∃ᶠ n in atTop, c < T n := by
    refine ⟨s m / 2, half_pos (hs m), ?_⟩
    apply hm.mono
    intro n hn
    simp only [T, ite_eq_left hn]
    exact half_lt_self (hs m)
  apply cofinal_local_intervals_of_frequently_scaled_horizons (μ ω)
    (fun n => R n ω) (fun n => A n ω) T hscale.1 hscale.2 hT
  intro n z hz hpos
  have hn : ω ∈ G m n := by
    by_contra hn
    simp only [T, ite_eq_right hn, mul_zero, lt_self_iff_false] at hpos
  simpa only [T, ite_eq_left hn] using hloc m n hn z hz

end HarmonicBalls
