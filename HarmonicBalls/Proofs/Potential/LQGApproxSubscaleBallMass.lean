import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.LQG.SingularApproximantUniformDyadic
import LatticeProb.LQG.NormalizedCircleAllScales
import LatticeProb.LQG.GMCOriginGrowth

/-!
# Singular approximation mass below the regularization scale

Dyadic circle-average approximations have a common insertion-centered ball bound
at all dyadic regularization scales.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

/-- Almost surely, singular approximations at every dyadic smoothing scale obey
an explicit common upper bound on sufficiently small dyadic balls at the origin. -/
theorem ae_singular_approximant_uniform_dyadic_ball_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, 0 < n ∧ ∃ J₀ : ℕ, ∀ J k : ℕ,
      dyadicScale J ≤ r → J₀ ≤ J / n →
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k) (ball 0 (dyadicScale J)) ≤
        max (ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
          Real.exp (-(Real.log 2) * J)))
          (ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
            (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ (J / n) /
              (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)))))) := by
  obtain ⟨H, hHc, _, _, hHr⟩ := hh.exists_continuous_circle_version
  let F : Ω → C(CircleParameter, ℝ) := fun ω =>
    ⟨fun p => H p.1 p.2 ω,
      continuousOn_univ.mp ((hHc ω).comp
        (continuous_subtype_val.prodMap continuous_id).continuousOn
        (by intro p _; exact ⟨p.1.2, mem_univ _⟩))⟩
  have hF : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2 :=
    fun p => hHr p.1 p.1.2 p.2
  have hcircle : ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ k z, z ∈ ball (0 : ℂ) r →
      H (LatticeProb.LQG.dyadicScale k) z ω ≤
        C + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ := by
    apply LatticeProb.LQG.ae_exists_all_dyadic_circle_le_of_normalized_gff
      (X := reconstructedGFF hC) (c := fun ω s z => H s z ω)
      hh.reconstructedGFF_normalized
      (fun ω => hHc ω) _ hδ hρ hrρ
    intro s hs z
    exact (hHr s hs z).trans (hh.ae_circleAvg_reconstructedGFF hs z)
  have hlp : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc :=
    (LPBridge.isWholePlaneGFF_iff P hC hcirc).mp hh
  filter_upwards [hcircle, hh.ae_circle_map_eq_raw hF,
    hlp.ae_eventually_exp_circle_mul_maximal_dilated_le hγ hγ2] with ω hc he hZ
  obtain ⟨C, hC, hc⟩ := hc
  have hc' : ∀ k z, z ∈ ball (0 : ℂ) r →
      hcirc ω (LatticeProb.LQG.dyadicScale k) z ≤
        C + (2 + δ) * Real.log (LatticeProb.LQG.dyadicScale k)⁻¹ := by
    intro k z hz
    have heq := he (⟨LatticeProb.LQG.dyadicScale k, by change 0 < LatticeProb.LQG.dyadicScale k; unfold LatticeProb.LQG.dyadicScale; positivity⟩, z)
    exact heq ▸ hc k z hz
  exact ⟨C, hC, LatticeProb.LQG.exists_singular_approximant_uniform_dyadic_bound
    hγ hαQ (hcirc ω) hc' hZ⟩

/-- The same event controls balls whose centers are at most their radius from
    the insertion. -/
theorem ae_singular_approximant_near_origin_dyadic_ball_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hrρ : r < ρ) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ, 0 < n ∧ ∃ J₀ : ℕ,
      ∀ J k : ℕ, ∀ z : ℂ, ‖z‖ ≤ dyadicScale (J + 1) →
      dyadicScale J ≤ r → J₀ ≤ J / n →
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)
          (ball z (dyadicScale (J + 1))) ≤
        max (ENNReal.ofReal (Real.pi * Real.exp (γ * C) *
          Real.exp (-(Real.log 2) * J)))
          (ENNReal.ofReal (Real.exp (γ * (|α| * Real.log 2)) *
            (Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)) ^ (J / n) /
              (1 - Real.exp (-(γ * (lqgQ γ - α) * Real.log 2 / 2)))))) := by
  filter_upwards [ae_singular_approximant_uniform_dyadic_ball_bound
    hh hγ hγ2 hαQ hδ hρ hrρ] with ω hω
  obtain ⟨C, hC, n, hn, J₀, hJ₀⟩ := hω
  refine ⟨C, hC, n, hn, J₀, fun J k z hz hr hJ => ?_⟩
  refine (measure_mono ?_).trans (hJ₀ J k hr hJ)
  intro x hx
  have hxz : ‖x - z‖ < dyadicScale (J + 1) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have htri := norm_add_le (x - z) z
  have hs : dyadicScale (J + 1) = dyadicScale J / 2 := by
    simp only [dyadicScale, pow_succ]
    ring
  have hx0 : ‖x‖ < dyadicScale J := by
    have heq : x - z + z = x := sub_add_cancel x z
    rw [heq] at htri
    linarith
  simpa only [Metric.mem_ball, dist_zero_right] using hx0

end HarmonicBalls
