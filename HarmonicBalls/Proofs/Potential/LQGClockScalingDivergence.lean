import HarmonicBalls.Proofs.Potential.LQGClockTimeChangeReduction

/-! # Divergence of a clock from a scaling identity

Bertacco and Gwynne (*Liouville Brownian motion and quantum cones in dimension `d > 2`*,
arXiv:2501.15936v2), proof of Theorem 5.12 (B4), which replaces the argument of Garban, Rhodes
and Vargas (2016, Theorem 2.7 (4)) based on the exponential decay of the correlations of the
massive free field by a scaling argument for the massless field. At the exit times `τ_n` of the
balls `B(0, n)` the clock factors as `F(τ_n) = c_n Y_n`, where the prefactor
`c_n = n^{γ Q} e^{γ h_n(0)}` tends to infinity almost surely (Borel-Cantelli, since `h_n(0)` is a
centered Gaussian of variance `log n`), and where `Y_n`, the clock of the rescaled field
`h(n ·) - h_n(0)` along the rescaled path up to its exit time of the unit ball, has a law not
depending on `n` and is almost surely positive (by the strict increase of the clock). Hence for
every `ε > 0` there is `δ > 0` with `P(Y_n ≥ δ) ≥ 1 - ε` for all `n`; by the continuity of measures
from above, `Y_n ≥ δ` for infinitely many `n` with probability at least `1 - ε`, and on that
event `F(τ_n) ≥ δ c_n` is unbounded. Since `ε` is arbitrary and the clock is nondecreasing, it
tends to infinity almost surely.

This file proves this deduction for an abstract nondecreasing clock under one probability
measure (the joint law of the field and the path), with the factorization, the divergence of
the prefactors, the equality of the laws of the `Y_n` and the positivity of `Y_0` as hypotheses,
and then the Fubini step to almost every field for clocks of planar Brownian motion.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- A nondecreasing function `F` with `c n * Y n ≤ F (τ n)` along a sequence of times, where
`c n → ∞` and `δ ≤ Y n` for infinitely many `n` with `δ > 0`, tends to infinity. -/
theorem tendsto_atTop_of_frequently_le_mul {F : ℝ≥0 → ℝ} (hF : Monotone F) {τ : ℕ → ℝ≥0}
    {c Y : ℕ → ℝ} (hscale : ∀ n, c n * Y n ≤ F (τ n)) (hc : Tendsto c atTop atTop) {δ : ℝ}
    (hδ : 0 < δ) (hY : ∀ N, ∃ n, N ≤ n ∧ δ ≤ Y n) : Tendsto F atTop atTop := by
  refine tendsto_atTop_atTop_of_monotone hF fun M => ?_
  obtain ⟨N, hN⟩ := (hc.eventually (eventually_ge_atTop (max M 0 / δ))).exists_forall_of_atTop
  obtain ⟨n, hnN, hnY⟩ := hY N
  refine ⟨τ n, ?_⟩
  have hcn : max M 0 / δ ≤ c n := hN n hnN
  have hc0 : 0 ≤ c n := le_trans (div_nonneg (le_max_right M 0) hδ.le) hcn
  calc M ≤ max M 0 := le_max_left M 0
    _ = max M 0 / δ * δ := by field_simp
    _ ≤ c n * δ := mul_le_mul_of_nonneg_right hcn hδ.le
    _ ≤ c n * Y n := mul_le_mul_of_nonneg_left hnY hc0
    _ ≤ F (τ n) := hscale n

/-- Bertacco-Gwynne 2025, proof of Theorem 5.12 (B4), for an abstract clock: under a probability
measure, if the clock is almost surely nondecreasing and dominates almost surely `c n * Y n` at the
times `τ n`, the prefactors `c n` tend to infinity almost surely, and the random variables `Y n`
are identically distributed and almost surely positive, then the clock tends to infinity almost
surely. -/
theorem ae_tendsto_atTop_of_le_mul_of_map_eq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    [IsProbabilityMeasure μ] (F : X → ℝ≥0 → ℝ) (τ : ℕ → X → ℝ≥0) (c Y : ℕ → X → ℝ)
    (hmono : ∀ᵐ p ∂μ, Monotone (F p))
    (hscale : ∀ n, ∀ᵐ p ∂μ, c n p * Y n p ≤ F p (τ n p))
    (hc : ∀ᵐ p ∂μ, Tendsto (fun n => c n p) atTop atTop)
    (hYm : ∀ n, Measurable (Y n)) (hlaw : ∀ n, μ.map (Y n) = μ.map (Y 0))
    (hpos : ∀ᵐ p ∂μ, 0 < Y 0 p) :
    ∀ᵐ p ∂μ, Tendsto (F p) atTop atTop := by
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
  have hgood : ∀ᵐ p ∂μ, Monotone (F p) ∧ Tendsto (fun n => c n p) atTop atTop ∧
      ∀ n, c n p * Y n p ≤ F p (τ n p) := by
    filter_upwards [hmono, hc, ae_all_iff.mpr hscale] with p h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨E, hEnull, hE⟩ : ∃ E : Set X, μ E = 0 ∧ ∀ p ∉ E, Monotone (F p) ∧
      Tendsto (fun n => c n p) atTop atTop ∧ ∀ n, c n p * Y n p ≤ F p (τ n p) :=
    ⟨_, ae_iff.mp hgood, fun p hp => by simpa using hp⟩
  have hbound (k : ℕ) : μ {p | ¬ Tendsto (F p) atTop atTop} ≤ μ {p | Y 0 p < δ k} := by
    have hsub : {p | ¬ Tendsto (F p) atTop atTop} ⊆ (L k)ᶜ ∪ E := by
      intro p hp
      by_contra hcon
      simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
      obtain ⟨hpL, hpE⟩ := hcon
      obtain ⟨hm, hcp, hs⟩ := hE p hpE
      refine hp (tendsto_atTop_of_frequently_le_mul hm hs hcp (hδ k) fun N => ?_)
      have hpU : p ∈ U k N := mem_iInter.mp hpL N
      simp only [U, mem_iUnion, mem_ofPred_eq] at hpU
      obtain ⟨j, hj⟩ := hpU
      exact ⟨N + j, Nat.le_add_right N j, hj⟩
    have hYlt : {p | Y 0 p < δ k} = {p | δ k ≤ Y 0 p}ᶜ := by
      ext p
      simp [not_le]
    calc μ {p | ¬ Tendsto (F p) atTop atTop} ≤ μ ((L k)ᶜ ∪ E) := measure_mono hsub
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
  have h0 : μ {p | ¬ Tendsto (F p) atTop atTop} = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) zero_le
  exact ae_iff.mpr h0

/-- The Fubini step: if a jointly defined clock tends to infinity almost surely under the product
of the field law and the law of planar Brownian motion, then for almost every field it tends to
infinity for almost every path. -/
theorem ae_ae_tendsto_atTop_of_ae_prod {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {x : ℂ} (G : Ω → ContinuousPath ℂ → ℝ≥0 → ℝ)
    (h : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), Tendsto (G p.1 p.2) atTop atTop) :
    ∀ᵐ ω ∂P, ∀ᵐ b ∂(planarBrownianMotion x), Tendsto (G ω b) atTop atTop :=
  Measure.ae_ae_of_ae_prod h

end HarmonicBalls
