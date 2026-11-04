import HarmonicBalls.Steps.Sec11.PinchStationaryFrequency

/-!
# One-scale expectations of a stationary tail

The stationarity assumption in the pinch-scale argument fixes all positive
scale expectations from the expectation at the first positive scale.
-/

open MeasureTheory Filter Finset
open scoped Topology BigOperators

namespace HarmonicBalls

/-- A stationary measurable tail has equal one-dimensional marginal laws. -/
theorem map_eq_first_of_stationary_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (n : ℕ) : P.map (X (n + 1)) = P.map (X 1) := by
  have hm1 : Measurable (fun ω n => X (n + 1) ω) :=
    Measurable.of_eval fun n => hXm (n + 1)
  have hm2 : Measurable (fun ω n => X (n + 2) ω) :=
    Measurable.of_eval fun n => hXm (n + 2)
  have hstep (n : ℕ) : P.map (X (n + 2)) = P.map (X (n + 1)) := by
    have h := congrArg (fun Q : Measure (ℕ → ℝ) => Q.map (fun x => x n)) hstat
    rw [Measure.map_map (measurable_pi_apply n) hm2,
      Measure.map_map (measurable_pi_apply n) hm1] at h
    exact h
  induction n with
  | zero => rfl
  | succ n ih => simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using (hstep n).trans ih

/-- A stationary measurable tail has a common one-scale expectation. -/
theorem integral_eq_first_of_stationary_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (n : ℕ) : (∫ ω, X (n + 1) ω ∂P) = ∫ ω, X 1 ω ∂P := by
  have h := map_eq_first_of_stationary_tail P X hXm hstat n
  calc
    (∫ ω, X (n + 1) ω ∂P) = ∫ x : ℝ, x ∂P.map (X (n + 1)) :=
      (integral_map (hXm (n + 1)).aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ x : ℝ, x ∂P.map (X 1) := by rw [h]
    _ = ∫ ω, X 1 ω ∂P :=
      integral_map (hXm 1).aemeasurable measurable_id.aestronglyMeasurable

/-- Stationarity supplies the common mean, so the limiting frequency is the
first positive-scale expectation. -/
theorem ae_tendsto_initialScaleAverage_of_stationary_tail_trivial_germ
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hXm : ∀ n, Measurable (X n))
    (hXbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1)
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω)) :
    ∀ᵐ ω ∂P, Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, X n ω) / (N : ℝ))
      atTop (𝓝 (∫ ω, X 1 ω ∂P)) := by
  let Y : ℕ → Ω → ℝ := fun n ω => if n = 0 then X 1 ω else X n ω
  have hYpos (n : ℕ) (hn : 1 ≤ n) : Y n = X n := by
    funext ω
    simp [Y, Nat.ne_of_gt (by omega : 0 < n)]
  have hYgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (Y n) := by
    intro ε hε
    obtain ⟨K, hK⟩ := hXgerm ε hε
    refine ⟨max K 1, fun n hn => ?_⟩
    rw [hYpos n (le_trans (le_max_right _ _) hn)]
    exact hK n (le_trans (le_max_left _ _) hn)
  have hYm : ∀ n, Measurable (Y n) := by
    intro n
    by_cases hn : n = 0
    · subst n; simpa [Y] using hXm 1
    · rw [hYpos n (by omega)]
      exact hXm n
  have hYbound : ∀ n ω, Y n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    by_cases hn : n = 0
    · subst n; simpa [Y] using hXbound 1 ω
    · rw [hYpos n (by omega)]
      exact hXbound n ω
  have heq1 : (fun ω n => Y (n + 1) ω) = (fun ω n => X (n + 1) ω) := by
    funext ω n
    rw [hYpos (n + 1) (by omega)]
  have heq2 : (fun ω n => Y (n + 2) ω) = (fun ω n => X (n + 2) ω) := by
    funext ω n
    rw [hYpos (n + 2) (by omega)]
  have hYBirkhoff : PointwiseBirkhoff (P.map (fun ω n => Y (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0) := by
    rw [heq1]
    exact hBirkhoff
  have hYstat : P.map (fun ω n => Y (n + 2) ω) = P.map (fun ω n => Y (n + 1) ω) := by
    rw [heq1, heq2]
    exact hstat
  have hYmean : ∀ n, ∫ ω, Y n ω ∂P = ∫ ω, X 1 ω ∂P := by
    intro n
    by_cases hn : n = 0
    · subst n; simp [Y]
    · rw [hYpos n (by omega)]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      simpa [Nat.succ_eq_add_one] using integral_eq_first_of_stationary_tail P X hXm hstat k
  have hlim := ae_tendsto_initialScaleAverage_of_stationary_trivial_germ P Y
    (∫ ω, X 1 ω ∂P) germ hgle hYgerm htrivial hYm hYbound hYBirkhoff hYstat hYmean
  filter_upwards [hlim] with ω hω
  convert hω using 1
  funext N
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [hYpos n (Finset.mem_Icc.mp hn).1]

open Classical in
/-- Fixed-point pinch block density follows from positive first-scale
expectation, stationarity, and the trivial-germ hypotheses. -/
theorem ae_eventually_pinchPointEvent_block_ncard_of_stationary_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Ω → Measure ℂ)
    (D : Ω → ℂ → ℂ → ℝ) (U T Q' Q : Set ℂ) (M : ℝ) (z : ℂ)
    (X : ℕ → Ω → ℝ) (δ : ℝ)
    (germ : ℝ → MeasurableSpace Ω) (hgle : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    (hXgerm : ∀ ε, 0 < ε → ∃ K, ∀ n, K ≤ n →
      @Measurable Ω ℝ (germ ε) _ (X n))
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε → MeasurableSet[germ ε] A) →
      P A = 0 ∨ P A = 1)
    (hXm : ∀ n, Measurable (X n))
    (hX : ∀ n ω, X n ω = if pinchPointEventWithInternalBounds (μ ω) (D ω)
      U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z then 1 else 0)
    (hBirkhoff : PointwiseBirkhoff (P.map (fun ω n => X (n + 1) ω))
      (fun x n => x (n + 1)) (fun x => x 0))
    (hstat : P.map (fun ω n => X (n + 2) ω) = P.map (fun ω n => X (n + 1) ω))
    (hδ : δ < ∫ ω, X 1 ω ∂P)
    (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, δ * N ≤
      ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ) := by
  have hbound : ∀ n ω, X n ω ∈ Set.Icc (0 : ℝ) 1 := by
    intro n ω
    rw [hX]
    split_ifs <;> norm_num
  have hlim := ae_tendsto_initialScaleAverage_of_stationary_tail_trivial_germ P X germ
    hgle hXgerm htrivial hXm hbound hBirkhoff hstat
  filter_upwards [hlim, hD] with ω hω hDω
  apply eventually_pinchPointEvent_block_ncard_of_internalFrequency hDω hδ
  simpa only [hX] using hω

end HarmonicBalls
