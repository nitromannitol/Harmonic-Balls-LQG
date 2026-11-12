import HarmonicBalls.FirstPass.Phase2.GFFExistsConstructed
import HarmonicBalls.FirstPass.Phase2.DomainMarkovMeanValue

/-!
# Circle averages as uniformly bounded probes of the outer field

Let `K` be compact inside an open set `W`. There is one radius `ε > 0` such that for every `x ∈ K` the closed disk
`B̄_ε(x)` lies in `W`, and the variances of the circle averages `h_ε(x)`, `x ∈ K`, of the whole-plane GFF are
bounded by one constant. For every mean-zero test function `ρ` supported outside `closure W`, the covariance of
`h_ε(x)` with `(h, ρ)` is the covariance potential `outerPotential ρ x` (mean value property). Together with Bessel's
inequality for pairwise uncorrelated outer pairings this bounds `∑_k Var((h, ρ_k))⁻¹ (outerPotential ρ_k x)²`
uniformly in `x ∈ K`.

## Main results

* `circleAverage_logMaxAbs_le`: the average of `log max(|·|, 1)` over `∂B_r(z)` is at most `|z| + |r|`.
* `wholePlaneGFFCov_circle_self_le`: `Var(h_r(z)) ≤ 2 (|z| + r) - log r`.
* `IsWholePlaneGFF.exists_circle_probe_of_isCompact`: the uniform radius, the uniform variance bound and the
  covariance identity with outer pairings.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric ProbabilityTheory

/-- The average of `logMaxAbs = log max(|·|, 1)` over the circle `∂B_r(z)` is at most `|z| + |r|`. -/
theorem circleAverage_logMaxAbs_le (z : ℂ) (r : ℝ) :
    Real.circleAverage logMaxAbs z r ≤ ‖z‖ + |r| := by
  refine Real.circleAverage_mono_on_of_le_circle
    (circleIntegrable_of_continuous continuous_logMaxAbs z r) fun x hx => ?_
  rw [mem_sphere_iff_norm] at hx
  have h1 : Real.log (max ‖x‖ 1) ≤ max ‖x‖ 1 - 1 :=
    Real.log_le_sub_one_of_pos (lt_of_lt_of_le one_pos (le_max_right _ _))
  have h2 : max ‖x‖ 1 ≤ ‖x‖ + 1 := max_le (by linarith [norm_nonneg x]) (by linarith [norm_nonneg x])
  have h3 := norm_sub_norm_le x z
  unfold logMaxAbs
  linarith

/-- The variance of a circle average of the whole-plane GFF: `Var(h_r(z)) ≤ 2 (|z| + r) - log r`. -/
theorem wholePlaneGFFCov_circle_self_le {r : ℝ} (hr : 0 < r) (z : ℂ) :
    wholePlaneGFFCov (.circle r z) (.circle r z) ≤ 2 * (‖z‖ + r) - Real.log r := by
  rw [wholePlaneGFFCov_circle_self_eq_sub_log hr z]
  have h := circleAverage_logMaxAbs_le z r
  rw [abs_of_pos hr] at h
  linarith

/-- **Circle averages as uniform probes of the outer field.** For `K` compact inside an open `W` there are a radius
`ε > 0` and a constant `M` such that, for every `x ∈ K`, `B̄_ε(x) ⊆ W`, `Var(h_ε(x)) ≤ M`, and the covariance of
`h_ε(x)` with the pairing `(h, ρ)` of every mean-zero test function `ρ` supported in `(closure W)ᶜ` is
`outerPotential ρ x`. -/
theorem IsWholePlaneGFF.exists_circle_probe_of_isCompact {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {K W : Set ℂ}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ ε M : ℝ, 0 < ε ∧ ∀ x ∈ K, closedBall x ε ⊆ W ∧ Var[fun s => hcirc s ε x; P] ≤ M ∧
      ∀ ρ : ℂ → ℝ, IsTestFunction (closure W)ᶜ ρ → ∫ y, ρ y = 0 →
        cov[fun s => hcirc s ε x, fun s => hC s ρ; P] = outerPotential ρ x := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open hW hKW
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hε : 0 < δ / 2 := half_pos hδ
  refine ⟨δ / 2, 2 * (R + δ / 2) - Real.log (δ / 2), hε, fun x hx => ⟨?_, ?_, ?_⟩⟩
  · intro y hy
    refine hsub (Metric.mem_thickening_iff.mpr ⟨x, hx, ?_⟩)
    rw [mem_closedBall] at hy
    linarith
  · have hxR : ‖x‖ ≤ R := by simpa using hR hx
    have hm : AEMeasurable (fun s => hcirc s (δ / 2) x) P := (hh.measurable_circle _ x hε).aemeasurable
    have hc : cov[fun s => hcirc s (δ / 2) x, fun s => hcirc s (δ / 2) x; P] =
        wholePlaneGFFCov (.circle (δ / 2) x) (.circle (δ / 2) x) :=
      hh.covariance_eq (.circle (δ / 2) x) (.circle (δ / 2) x) hε hε
    rw [← covariance_self hm, hc]
    have := wholePlaneGFFCov_circle_self_le hε x
    linarith
  · intro ρ hρ h0
    have hball : closedBall x (δ / 2) ⊆ W := fun y hy =>
      hsub (Metric.mem_thickening_iff.mpr ⟨x, hx, by rw [mem_closedBall] at hy; linarith⟩)
    exact hh.covariance_circle_pairing_eq_outerPotential (hρ.mono_set (subset_univ _)) h0 hε
      ((disjoint_compl_right.mono_right hρ.2.2).mono_left (hball.trans subset_closure))

end HarmonicBalls
