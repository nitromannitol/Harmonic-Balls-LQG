import HarmonicBalls.Proofs.Sec6.LQGWeylScaling

/-!
# Weyl density step of the measure half of the rooted local rescaling (fp-S11as, round 4)

Two whole-plane fields whose circle averages differ by the circle averages of a continuous function `v`
(`hcirc' = hcirc + circleAverage v`) have, almost surely, LQG measures (background `α`, insertion `γ`) related by the
Weyl density `exp(γ v)`: the coordinate change `h ↦ h + v` of Duplantier–Sheffield (the LQG measure of a continuous shift
is the measure weighted by `e^{γ v}`, Berestycki–Powell). Proof: the approximations of the shifted field are the
approximations of the original plus the circle averages of `v` (`addCircleAverage`); `Section6.isLQGLimit_addCircleAverage`
identifies the weighted limit, and `IsLQGLimit.unique` identifies the two measures.

Locality: where `v = 0` the density is `1`, so the two measures agree on that set (Armitage–Gardiner: the set on which the
shift vanishes). The only probabilistic input is the almost sure continuity of the circle averages at the dyadic scales,
taken as the hypothesis `hcont`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls

namespace FirstPassS11asWeyl

/-- The circle averages of `h + v` are those of `h` plus the circle averages of `v`. -/
theorem fieldCircleAverage_eq_addCircleAverage {α : ℝ} {hcirc hcirc' : ℝ → ℂ → ℝ} {v : ℂ → ℝ}
    (hshift : ∀ r x, hcirc' r x = hcirc r x + Real.circleAverage v x r) :
    fieldCircleAverage α hcirc' = addCircleAverage (fieldCircleAverage α hcirc) v := by
  funext r x
  simp only [fieldCircleAverage, addCircleAverage, hshift]
  ring

/-- **Weyl density under a continuous shift (almost surely).** If `hcirc'` is `hcirc` shifted by the circle averages of a
continuous `v`, and both LQG measures exist, then almost surely `μ' = e^{γ v} · μ`. -/
theorem lqgMeasure_eq_withDensity_of_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} {v : ℂ → ℝ} (hv : Continuous v)
    (hshift : ∀ ω r x, hcirc' ω r x = hcirc ω r x + Real.circleAverage v x r)
    (hcont : ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale n)))
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμ' : IsLQGMeasureOfField P γ α hcirc' μ') :
    ∀ᵐ ω ∂P, μ' ω = (μ ω).withDensity fun x => ENNReal.ofReal (Real.exp (γ * v x)) := by
  have hμ0 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
  have hμ1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc' ω)) (μ' ω) := hμ'
  filter_upwards [hμ0, hμ1, hcont] with ω h1 h2 h3
  have hsh : fieldCircleAverage α (hcirc' ω) = addCircleAverage (fieldCircleAverage α (hcirc ω)) v :=
    fieldCircleAverage_eq_addCircleAverage (fun r x => hshift ω r x)
  rw [hsh] at h2
  have h4 := Section6.isLQGLimit_addCircleAverage h1 h3 v hv
  exact IsLQGLimit.unique h2 h4

/-- **Locality of the Weyl density (almost surely).** If the shift `v` vanishes on a measurable set `S`, then the two LQG
measures agree on `S`: `(μ' ω).restrict S = (μ ω).restrict S`. -/
theorem lqgMeasure_restrict_eq_of_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ} {μ μ' : Ω → Measure ℂ} {v : ℂ → ℝ} (hv : Continuous v)
    (hshift : ∀ ω r x, hcirc' ω r x = hcirc ω r x + Real.circleAverage v x r)
    (hcont : ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale n)))
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμ' : IsLQGMeasureOfField P γ α hcirc' μ')
    {S : Set ℂ} (hS : MeasurableSet S) (hv0 : ∀ x ∈ S, v x = 0) :
    ∀ᵐ ω ∂P, (μ' ω).restrict S = (μ ω).restrict S := by
  filter_upwards [lqgMeasure_eq_withDensity_of_shift hv hshift hcont hμ hμ'] with ω hω
  rw [hω, restrict_withDensity hS]
  have hdens : (fun x => ENNReal.ofReal (Real.exp (γ * v x))) =ᵐ[(μ ω).restrict S] fun _ => 1 := by
    filter_upwards [ae_restrict_mem hS] with x hx
    simp [hv0 x hx]
  rw [withDensity_congr_ae hdens]; exact withDensity_one

end FirstPassS11asWeyl
