import HarmonicBalls.Proofs.Potential.ReflectedClockOccupation

/-!
# The occupation identity of a clock from every start

Let `A` be a clock of reflected Brownian motion in `K₀` (`IsUnitSquarePCAF A`), unbounded from
every start in `K₀`, with finite Revuz measure `ν`, and `k_s(x, y)` the Neumann heat kernel of the
square. For every start `x ∈ K₀` and every window `(a, T]` with `a > 0`,
`E_x ∫_{(a,T]} g(b_s) dA_s = ∫_a^T ∫ k_s(x, y) g(y) ν(dy) ds`
(`lintegral_clockOccupation_windowWeight_eq`). The proof partitions `(a, T]` at
`a = s_0 < ⋯ < s_N = T`: by the Markov property at `s_j` and the stationarity of Lebesgue measure,
`E_x ∫_{(s_j, s_{j+1}]} g dA = E_m[k_{s_j}(x, b_{s_j}) ∫_{(s_j, s_{j+1}]} g dA]`, where `E_m` is
reflected Brownian motion started from Lebesgue measure on `K₀`; as the mesh tends to `0` the
weights converge along every path to `k_s(x, b_s)` by continuity of the kernel, and dominated
convergence and the mean occupation measure `ds ⊗ ν` under `E_m`
(`lebesgueOccupationMeasure_eq_prod`) give the identity.
-/

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- **Windows after a fixed time.** Almost surely, for every measurable `g`, the occupation
integral over `(c, c + h]` along `b` is the occupation integral over `(0, h]` along `θ_c b`. -/
theorem ae_clockOccupation_windowWeight_shift {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {z : ℂ} (hz : z ∈ closedSquare 0 1)
    (hU : ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, Tendsto (fun t => A t b) atTop atTop)
    (c : ℝ≥0) (h : ℝ) :
    ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z, ∀ g : ℂ → ℝ≥0∞, Measurable g →
      clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b =
        clockOccupation A (windowWeight (Ioc 0 h) g) (ContinuousPath.shift c b) := by
  filter_upwards [ae_clockOccupation_indicator_Ioi_eq_shift hA hz hU c] with b hb g hg
  have h1 := hb (windowWeight (Ioc (c : ℝ) (c + h)) g)
    (measurable_windowWeight measurableSet_Ioc hg)
  have e1 : (fun p : ℝ × ℂ => (Ioi (c : ℝ)).indicator (fun _ =>
      windowWeight (Ioc (c : ℝ) (c + h)) g p) p.1) = windowWeight (Ioc (c : ℝ) (c + h)) g := by
    funext p
    by_cases hp : p.1 ∈ Ioc (c : ℝ) (c + h)
    · simp [indicator, show p.1 ∈ Ioi (c : ℝ) from hp.1]
    · simp [windowWeight, indicator, hp, mem_prod]
  have e2 : (fun p : ℝ × ℂ => windowWeight (Ioc (c : ℝ) (c + h)) g ((c : ℝ) + p.1, p.2)) =
      windowWeight (Ioc 0 h) g := by
    funext p
    have : (c : ℝ) + p.1 ∈ Ioc (c : ℝ) (c + h) ↔ p.1 ∈ Ioc (0 : ℝ) h := by
      simp only [mem_Ioc]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
    by_cases hp : p.1 ∈ Ioc (0 : ℝ) h
    · simp [windowWeight, indicator, mem_prod, hp, this.2 hp]
    · simp [windowWeight, indicator, mem_prod, hp, mt this.1 hp]
  rw [e1, e2] at h1
  exact h1

/-- **The Markov property at a fixed time with the Neumann kernel**:
`E_x Ψ(θ_c b) = ∫_{K₀} E_y Ψ k_c(x, y) dy` for `c > 0`. -/
theorem lintegral_shift_eq_neumannKernel {Ψ : ContinuousPath ℂ → ℝ≥0∞} (hΨ : Measurable Ψ)
    (x : ℂ) {c : ℝ≥0} (hc : c ≠ 0) :
    ∫⁻ b, Ψ (ContinuousPath.shift c b) ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ y in closedSquare 0 1, (∫⁻ b, Ψ b ∂reflectedPlanarBrownianMotion 0 1 y) *
        squareNeumannKernel c x y := by
  have hφ : Measurable fun y => ∫⁻ b, Ψ b ∂reflectedPlanarBrownianMotion 0 1 y :=
    hΨ.lintegral_kernel
  have h := lintegral_reflected_eval_mul_shift (g := fun _ => 1) measurable_const hΨ c x
  simp only [one_mul] at h
  rw [h, ← lintegral_reflected_eval_eq_neumannKernel hφ x hc, lintegral_reflected_eval_eq c hφ x]
  refine lintegral_congr fun w => ?_
  rw [reflectedPlanarBrownianMotion_zero_one_squareFold]

/-- **One window from every start.** For `x ∈ K₀`, `c > 0` and `h`,
`E_x ∫_{(c, c+h]} g dA = E_m[k_c(x, b_c) ∫_{(c, c+h]} g dA]`. -/
theorem lintegral_clockOccupation_window_eq {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A)
    (hU : ∀ z ∈ closedSquare 0 1, ∀ᵐ b ∂reflectedPlanarBrownianMotion 0 1 z,
      Tendsto (fun t => A t b) atTop atTop)
    {x : ℂ} (hx : x ∈ closedSquare 0 1) {c : ℝ≥0} (hc : c ≠ 0) (h : ℝ) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ b, clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b
        ∂reflectedPlanarBrownianMotion 0 1 x =
      ∫⁻ z in closedSquare 0 1, ∫⁻ b, squareNeumannKernel c x (b c) *
        clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b
          ∂reflectedPlanarBrownianMotion 0 1 z := by
  have hKm : MeasurableSet (closedSquare 0 1) :=
    (isCompact_closedSquare 0 1).isClosed.measurableSet
  have hΨ : Measurable (clockOccupation A (windowWeight (Ioc 0 h) g)) :=
    measurable_clockOccupation hA.measurable (measurable_windowWeight measurableSet_Ioc hg)
  have hk : Measurable fun y => squareNeumannKernel c x y :=
    (measurable_squareNeumannKernel c).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_congr_ae ((ae_clockOccupation_windowWeight_shift hA hx (hU x hx) c h).mono
    fun b hb => hb g hg), lintegral_shift_eq_neumannKernel hΨ x hc]
  have h2 : ∀ z ∈ closedSquare 0 1, ∫⁻ b, squareNeumannKernel c x (b c) *
      clockOccupation A (windowWeight (Ioc (c : ℝ) (c + h)) g) b
        ∂reflectedPlanarBrownianMotion 0 1 z =
      ∫⁻ b, squareNeumannKernel c x (b c) *
        clockOccupation A (windowWeight (Ioc 0 h) g) (ContinuousPath.shift c b)
          ∂reflectedPlanarBrownianMotion 0 1 z := by
    intro z hz
    refine lintegral_congr_ae ?_
    filter_upwards [ae_clockOccupation_windowWeight_shift hA hz (hU z hz) c h] with b hb
    rw [hb g hg]
  rw [setLIntegral_congr_fun hKm h2, setLIntegral_lintegral_mul_shift_eq hk hΨ c]
  refine setLIntegral_congr_fun hKm fun y _ => ?_
  rw [mul_comm]

/-- Windows of a monotone sequence of times add up. -/
theorem windowWeight_Ioc_eq_sum {f : ℕ → ℝ} (hf : Monotone f) (g : ℂ → ℝ≥0∞) (n : ℕ) :
    windowWeight (Ioc (f 0) (f n)) g =
      ∑ j ∈ Finset.range n, windowWeight (Ioc (f j) (f (j + 1))) g := by
  induction n with
  | zero => funext p; simp [windowWeight, indicator]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    funext p
    simp only [Pi.add_apply, windowWeight, indicator, mem_prod, mem_univ, and_true]
    have hmono : f 0 ≤ f n := hf (Nat.zero_le n)
    have hmono' : f n ≤ f (n + 1) := hf (Nat.le_succ n)
    by_cases h1 : p.1 ∈ Ioc (f 0) (f n)
    · have h2 : p.1 ∉ Ioc (f n) (f (n + 1)) := fun h => absurd h.1 (not_lt.2 h1.2)
      have h3 : p.1 ∈ Ioc (f 0) (f (n + 1)) := ⟨h1.1, h1.2.trans hmono'⟩
      simp [h1, h2, h3]
    · by_cases h2 : p.1 ∈ Ioc (f n) (f (n + 1))
      · have h3 : p.1 ∈ Ioc (f 0) (f (n + 1)) := ⟨lt_of_le_of_lt hmono h2.1, h2.2⟩
        simp [h1, h2, h3]
      · have h3 : p.1 ∉ Ioc (f 0) (f (n + 1)) := by
          rintro ⟨h4, h5⟩
          by_cases h6 : p.1 ≤ f n
          · exact h1 ⟨h4, h6⟩
          · exact h2 ⟨not_le.1 h6, h5⟩
        simp [h1, h2, h3]

end HarmonicBalls
