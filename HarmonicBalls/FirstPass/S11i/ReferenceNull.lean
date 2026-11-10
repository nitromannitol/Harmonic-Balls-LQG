import HarmonicBalls.FirstPass.S11w

/-!
# Reference null set of the pinch-window observation (fp-S11i-11-13; write-up `CHATGPT-n3-B1-B2.md` sec. 5.2, eqs (29), (31), (32))

For a family `c n` of certificate indicators on the reference observations, the window average over the dyadic window
`(N, 2N]` is `B_N` of eq. (29); the bad set `S` is where `B_N` does not converge to `q` (eq. (29)). If, for Lebesgue-almost
every root `z` in a ball `B_{r₁}(c₁)`, almost surely the window average of the reference observation at `z` converges to `q`
(this is the identification (31), supplied by the local decoder result and the rooted window limit), then the Campbell
integral of `1_S` against the LQG measure is almost surely zero (eq. (32)). The Campbell step is the discharged glue
`HarmonicBalls.S11w.ae_marked_null_of_reference_null_discharged` (FirstPass/S11w.lean).

NEW, deterministic plus the glue: no new input. The window-convergence hypothesis `hWin` is an explicit hypothesis.
-/

namespace HarmonicBalls.ReferenceNullS11i

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls

universe u

/-- The window average `B_N` of eq. (29): `(1/N) ∑_{n = N+1}^{2N} c_n(x)`. -/
noncomputable def refWindowAverage {X : Type*} (c : ℕ → X → ℝ) (N : ℕ) (x : X) : ℝ :=
  (∑ n ∈ Finset.Icc (N + 1) (2 * N), c n x) / (N : ℝ)

/-- The bad set `S` of eq. (29): the window averages `B_N(x)` do not converge to `q`. -/
def refBadWindowSet {X : Type*} (c : ℕ → X → ℝ) (q : ℝ) : Set X :=
  {x | ¬ Tendsto (fun N : ℕ => refWindowAverage c N x) atTop (𝓝 q)}

/-- The bad set is measurable when every `c n` is measurable (Mathlib `measurableSet_tendsto`). -/
theorem measurableSet_refBadWindowSet {X : Type*} [MeasurableSpace X] (c : ℕ → X → ℝ)
    (hc : ∀ n, Measurable (c n)) (q : ℝ) : MeasurableSet (refBadWindowSet c q) := by
  have hwa : ∀ N : ℕ, Measurable (refWindowAverage c N) := fun N => by
    unfold refWindowAverage
    exact (Finset.measurable_sum _ fun n _ => hc n).div_const _
  exact (measurableSet_tendsto (l := atTop) (𝓝 q) (f := fun N => refWindowAverage c N) hwa).compl

/-- An almost sure non-membership in `S` makes the lower integral of `1_S` vanish. -/
theorem lintegral_indicator_eq_zero_of_ae_notMem {Ω X : Type*} [MeasurableSpace Ω] {P : Measure Ω} (S : Set X)
    (f : Ω → X) (hf : ∀ᵐ ω ∂P, f ω ∉ S) :
    ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (f ω) ∂P = 0 := by
  calc ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (f ω) ∂P = ∫⁻ _ : Ω, 0 ∂P :=
        lintegral_congr_ae (by filter_upwards [hf] with ω hω; exact Set.indicator_of_notMem hω _)
    _ = 0 := lintegral_zero

/-- **Eq. (31) to eq. (32).** Let `c n` be measurable indicators on `X`, `q` the window limit, and let `hWin` say that for
Lebesgue-almost every root `z` in `ball c₁ r₁`, almost surely the window average at the reference observation converges to
`q`. Then almost surely the mark-weighted Campbell integral of the bad set `S = refBadWindowSet c q` over `ball c₁ r₁` vanishes.
The side conditions of the glue (`hfin`, `hmeas`) are discharged inside `S11w`. -/
theorem ae_marked_window_null (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < HarmonicBalls.lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : HarmonicBalls.IsWholePlaneGFF P hC hcirc) (hμ : HarmonicBalls.IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hE : ∀ n : ℕ, HarmonicBalls.LQGMeasureExistence P γ (HarmonicBalls.lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // HarmonicBalls.IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    (hc : ∀ n, Measurable (c n)) (q : ℝ)
    (hWin : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P,
      Tendsto (fun N : ℕ => refWindowAverage c N
        (HarmonicBalls.campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)) atTop (𝓝 q)) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      (refBadWindowSet c q).indicator (fun _ => (1 : ℝ≥0∞))
        (HarmonicBalls.campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
  have href : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)),
      ∫⁻ ω, (refBadWindowSet c q).indicator (fun _ => (1 : ℝ≥0∞))
        (HarmonicBalls.campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) ∂P = 0 := by
    filter_upwards [hWin] with z hz
    exact lintegral_indicator_eq_zero_of_ae_notMem _ _ (by filter_upwards [hz] with ω hω; exact fun h => h hω)
  exact HarmonicBalls.S11w.ae_marked_null_of_reference_null_discharged hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0
    (measurableSet_refBadWindowSet c hc q) href

end HarmonicBalls.ReferenceNullS11i

#print axioms HarmonicBalls.ReferenceNullS11i.ae_marked_window_null
