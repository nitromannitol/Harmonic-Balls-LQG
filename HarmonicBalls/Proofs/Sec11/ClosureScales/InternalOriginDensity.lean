import HarmonicBalls.Proofs.Sec11.ClosureScales.CertificateBlockDensity
import HarmonicBalls.Steps.Sec11.PinchStationaryMean
import HarmonicBalls.Proposed.Birkhoff

/-!
# Internal pinch block density at the origin under a stationary, germ-trivial law

Written argument `notes/sec11-proof/sec11-proof.tex`, draft lines 536-563: the pointwise ergodic theorem
(Birkhoff, LatticeProb, Leonardo Bonanno, via `HarmonicBalls.Proposed.Birkhoff`), the stationarity of the
dyadic-scale indicator sequence, and the choice of a rate `δ` strictly below the probability of the scale-one
event. The prefix-to-block step is `tendsto_block_average_of_prefix_average` (`CertificateBlockDensity.lean`).

Here the indicator sequence is the internal-bounds pinch indicator at the origin, `X n ω = 1[internal pinch at
scale 2^{-n}]`. The law `Q` is an arbitrary probability measure on the sample space. The statement is generic in
`Q` so that it can be applied to a rooted (recentred) law in the typical-point transfer (draft 565-649).

Explicit hypotheses (open steps, not literature inputs): measurability of the indicators (`hXm`, the pinch events
are measurable for the law), germ-measurability for large `n` (`hXgerm`, locality), germ triviality (`htrivial`,
draft 515-534), stationarity of the indicator law (`hstat`, draft 515-530), and the rate bound (`hδ`).

Proved here: the origin block density `∀ᵐ ω ∂Q, ∀ᶠ N, δ N ≤ #{k ∈ [N+1, 2N] : internal pinch at scale 2^{-k}}`.
The mean of the first indicator equals that of the scale-one indicator by stationarity (marginal argument).
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Shift of the stationarity relation: if the law of `(X (n+1))_n` equals the law of `(X n)_n`, then the law of
`(X (n+2))_n` equals the law of `(X (n+1))_n` (apply the coordinate shift to both sides). -/
theorem map_shift_stationary_of_first_shift {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω)
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hstat : Q.map (fun ω n => X (n + 1) ω) = Q.map (fun ω n => X n ω)) :
    Q.map (fun ω n => X (n + 2) ω) = Q.map (fun ω n => X (n + 1) ω) := by
  have hS : Measurable (fun x : ℕ → ℝ => fun n => x (n + 1)) :=
    Measurable.of_eval (fun n => measurable_pi_apply (n + 1))
  have hY : Measurable (fun ω n => X (n + 1) ω) := Measurable.of_eval (fun n => hXm (n + 1))
  have hX : Measurable (fun ω n => X n ω) := Measurable.of_eval (fun n => hXm n)
  calc Q.map (fun ω n => X (n + 2) ω) = Q.map ((fun x : ℕ → ℝ => fun n => x (n + 1)) ∘
        (fun ω n => X (n + 1) ω)) := rfl
    _ = (Q.map (fun ω n => X (n + 1) ω)).map (fun x : ℕ → ℝ => fun n => x (n + 1)) :=
        (Measure.map_map hS hY).symm
    _ = (Q.map (fun ω n => X n ω)).map (fun x : ℕ → ℝ => fun n => x (n + 1)) := by rw [hstat]
    _ = Q.map ((fun x : ℕ → ℝ => fun n => x (n + 1)) ∘ (fun ω n => X n ω)) :=
        Measure.map_map hS hX
    _ = Q.map (fun ω n => X (n + 1) ω) := rfl

open Classical in
/-- Internal pinch block density at the origin, under a probability law `Q` on the sample space with stationary
germ-trivial dyadic indicators, for any rate `δ` below the scale-one internal pinch probability (draft 536-563). -/
theorem internal_block_density_of_stationary_germ_law
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ) (U T Q' Qset : Set ℂ) (M : ℝ)
    (X : ℕ → Ω → ℝ) (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hX : ∀ n ω, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
        ((2 : ℝ)⁻¹ ^ n) 0 then (1 : ℝ) else 0)
    (hXm : ∀ n, Measurable (X n))
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) → Q A = 0 ∨ Q A = 1)
    (hstat : Q.map (fun ω n => X (n + 1) ω) = Q.map (fun ω n => X n ω))
    (δ : ℝ)
    (hδ : δ < (Q {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
        ((2 : ℝ)⁻¹ ^ 0) 0}).toReal) :
    ∀ᵐ ω ∂Q, ∀ᶠ N : ℕ in atTop,
      δ * N ≤ ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) 0}.ncard : ℝ) := by
  have hXbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    rw [hX n ω]
    split_ifs <;> norm_num
  have hfin : IsFiniteMeasure (Q.map (fun ω n => X (n + 1) ω)) := Q.isFiniteMeasure_map _
  have hBirk : PointwiseBirkhoff (Q.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0) :=
    pointwiseBirkhoff_of_latticeProb _ _ _
  have hlim := ae_tendsto_initialScaleAverage_of_stationary_tail_trivial_germ Q X germ hgle hXgerm
    htrivial hXm hXbound hBirk (map_shift_stationary_of_first_shift Q X hXm hstat)
  -- Stationarity of the law of the first coordinate: the mean of `X 1` equals the mean of `X 0`.
  have hmean10 : ∫ ω, X 1 ω ∂Q = ∫ ω, X 0 ω ∂Q := by
    have hmeas1 : Measurable (fun ω n => X (n + 1) ω) := Measurable.of_eval (fun n => hXm (n + 1))
    have hmeas0 : Measurable (fun ω n => X n ω) := Measurable.of_eval (fun n => hXm n)
    have h : ∫ x, x 0 ∂(Q.map (fun ω n => X (n + 1) ω)) =
        ∫ x, x 0 ∂(Q.map (fun ω n => X n ω)) := by
      rw [hstat]
    rw [integral_map hmeas1.aemeasurable (measurable_pi_apply 0).aestronglyMeasurable,
      integral_map hmeas0.aemeasurable (measurable_pi_apply 0).aestronglyMeasurable] at h
    simpa using h
  -- The mean of `X 0` is the probability of the scale-one internal event.
  have hE0 : MeasurableSet {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
      ((2 : ℝ)⁻¹ ^ 0) 0} := by
    have hset : {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
        ((2 : ℝ)⁻¹ ^ 0) 0} = X 0 ⁻¹' ({1} : Set ℝ) := by
      ext ω
      simp only [Set.mem_ofPred_eq, mem_preimage, mem_singleton_iff, hX 0 ω]
      simp
    rw [hset]
    exact hXm 0 (measurableSet_singleton 1)
  have hm : ∫ ω, X 0 ω ∂Q = (Q {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
      ((2 : ℝ)⁻¹ ^ 0) 0}).toReal := by
    have hfun : (fun ω => X 0 ω) = fun ω => if ω ∈ {ω | pinchPointEventWithInternalBounds (μ ω) (D ω)
        U T Q' Qset M ((2 : ℝ)⁻¹ ^ 0) 0} then (1 : ℝ) else 0 := by
      funext ω
      rw [hX 0 ω]
      simp only [Set.mem_ofPred_eq]
    rw [hfun]
    exact integral_event_indicator_eq_measureReal Q _ hE0
  -- Block-average limit for almost every sample point.
  filter_upwards [hlim] with ω hω
  have hlim' : Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N, X n ω) / (N : ℝ)) atTop
      (𝓝 ((Q {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
        ((2 : ℝ)⁻¹ ^ 0) 0}).toReal)) := by
    rw [← hm, ← hmean10]
    exact hω
  have hblock := tendsto_block_average_of_prefix_average (fun n => X n ω) hlim'
  have hδm : δ < (Q {ω | pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M
      ((2 : ℝ)⁻¹ ^ 0) 0}).toReal := hδ
  have hev := (tendsto_order.1 hblock).1 δ hδm
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hsum : δ * N < ∑ n ∈ Finset.Icc (N + 1) (2 * N), X n ω := (lt_div_iff₀ hNpos).1 hN
  have hset : ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
      pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) 0}) =
      ↑((Finset.Icc (N + 1) (2 * N)).filter
        (fun k => pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) 0)) := by
    ext k
    simp [Finset.mem_Icc, and_assoc]
  have hcard : ∑ n ∈ Finset.Icc (N + 1) (2 * N), X n ω =
      (({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEventWithInternalBounds (μ ω) (D ω) U T Q' Qset M ((2 : ℝ)⁻¹ ^ k) 0}).ncard : ℝ) := by
    rw [hset, Set.ncard_coe_finset]
    rw [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    rw [hX n ω]
  linarith

end HarmonicBalls
#print axioms HarmonicBalls.map_shift_stationary_of_first_shift
#print axioms HarmonicBalls.internal_block_density_of_stationary_germ_law
