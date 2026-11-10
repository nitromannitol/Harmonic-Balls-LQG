import HarmonicBalls.FirstPass.S11q

/-!
# Measure half of the rescaling hypothesis `hscale` (Lemma 11.13, write-up sec. 6 / eq. (30)-(32))

The LQG measure of the dyadically dilated field `h^{(R)}`, `R = 2^k`, is the designated limit with circle averages
`dilatedCircleAverage H R`. By `isLQGLimit_dilate_dyadic` (FirstPass/S11q.lean, n1's Step 12 coordinate identities) this
limit is `e^{-γ c_R} · (μ_h).map (· / R)`; `IsLQGLimit.unique` (Defs/LQG.lean) identifies the designated measure.
Only the LQG limit characterisation is used; no metric input. The metric half of `hscale` is not here.
-/

namespace HarmonicBalls.DilateMeasure

open MeasureTheory Filter Topology
open scoped ENNReal

/-- Deterministic identification: any measure `m'` that is the LQG limit of the dyadically dilated circle averages of
`H` equals `e^{-γ c_R} • (m).map (· / R)`, where `m` is the LQG limit of `H`. -/
theorem dyadic_dilate_measure_eq {γ : ℝ} {H : ℝ → ℂ → ℝ} {m m' : Measure ℂ} (hm : IsLQGLimit γ H m) (hγ : 0 < γ)
    (k : ℕ) (hmeas : ∀ r : ℝ, 0 < r → Measurable (H r))
    (hm' : IsLQGLimit γ (dilatedCircleAverage H ((2 : ℝ) ^ k)) m') :
    m' = ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ H ((2 : ℝ) ^ k))))
      • m.map (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ)) :=
  (IsLQGLimit.unique (isLQGLimit_dilate_dyadic hm hγ k hmeas) hm').symm

/-- Almost sure form, for a family of models indexed by `ω`: if `μ ω` is the LQG limit of `H ω` and `μk ω` is the LQG
limit of the `2^k`-dilation of `H ω` for almost every `ω`, then `μk ω = e^{-γ c_R} • (μ ω).map (· / R)` almost surely,
with the constant `c_R` of `H ω`. -/
theorem ae_dyadic_dilate_measure_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {γ : ℝ}
    (H : Ω → ℝ → ℂ → ℝ) (μ μk : Ω → Measure ℂ) (hγ : 0 < γ) (k : ℕ)
    (hmeas : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → Measurable (H ω r))
    (hμ : ∀ᵐ ω ∂P, IsLQGLimit γ (H ω) (μ ω))
    (hμk : ∀ᵐ ω ∂P, IsLQGLimit γ (dilatedCircleAverage (H ω) ((2 : ℝ) ^ k)) (μk ω)) :
    ∀ᵐ ω ∂P, μk ω = ENNReal.ofReal (Real.exp (-(γ * dilationConstant γ (H ω) ((2 : ℝ) ^ k))))
      • (μ ω).map (fun w : ℂ => w / (((2 : ℝ) ^ k : ℝ) : ℂ)) := by
  filter_upwards [hmeas, hμ, hμk] with ω hm hμω hμkω
  exact dyadic_dilate_measure_eq hμω hγ k hm hμkω

end HarmonicBalls.DilateMeasure
