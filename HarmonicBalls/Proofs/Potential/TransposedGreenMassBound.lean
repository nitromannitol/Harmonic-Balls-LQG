import HarmonicBalls.Proofs.Potential.GeneralDomainGreenProductIntegrability

/-!
# Uniform mass bound for transposed Green potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology

/-- Planar volume has a uniform bound for disc Green rows. -/
theorem disc_green_volume_row_bound {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ closedBall (0 : ℂ) R,
      Integrable (greenFunction (ball 0 R) y) (volume.restrict (ball 0 R)) ∧
      (∫ x in ball (0 : ℂ) R, greenFunction (ball 0 R) y x) ≤ C := by
  obtain ⟨_, _, r₀, hr₀, hg⟩ := volumeGrowth_volume R
  have hup : ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      volume (ball z r) ≤ ENNReal.ofReal (r ^ (1 : ℝ)) := by
    intro r hr hrr z hz
    exact (hg r hr hrr z hz).2
  exact green_disc_integral_bound_of_upper hR hr₀ (by norm_num : (0 : ℝ) < 1)
    hup (measure_ball_lt_top (μ := volume)).ne

/-- A uniform mass bound, including the integrability required by Fubini. -/
theorem transposedGreen_mass_bound {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {V : Set ℂ}, IsOpen V → V ⊆ ball 0 R →
      ∀ (ν : Measure ℂ) [IsFiniteMeasure ν], (∀ᵐ y ∂ν, y ∈ V) →
      IntegrableOn (fun x => ∫ y, greenFunction V y x ∂ν) V ∧
      (∀ᵐ x ∂(volume.restrict V), Integrable (fun y => greenFunction V y x) ν) ∧
      (∀ᵐ y ∂ν, Integrable (fun x => greenFunction V y x) (volume.restrict V)) ∧
      0 ≤ (∫ x in V, ∫ y, greenFunction V y x ∂ν) ∧
      (∫ x in V, ∫ y, greenFunction V y x ∂ν) ≤ C * (ν Set.univ).toReal := by
  obtain ⟨C, hC, hrow⟩ := disc_green_volume_row_bound hR
  refine ⟨C, hC, ?_⟩
  intro V hV hsub ν _ hν
  have hVb : Bornology.IsBounded V := isBounded_ball.subset hsub
  have hp := generalDomain_green_integrable_product_volume hV hVb hν
  have hrowV : ∀ᵐ y ∂ν,
      (∫ x in V, greenFunction V y x) ≤ C := by
    filter_upwards [hν, hp.prod_right_ae] with y hy hi
    have hd := hrow y (ball_subset_closedBall (hsub hy))
    calc
      (∫ x in V, greenFunction V y x) ≤
          ∫ x in V, greenFunction (ball 0 R) y x := by
        apply integral_mono_ae hi (hd.1.mono_measure (Measure.restrict_mono hsub le_rfl))
        exact Eventually.of_forall fun x => Section6.greenFunction_le_of_subset hsub isBounded_ball y x
      _ ≤ ∫ x in ball (0 : ℂ) R, greenFunction (ball 0 R) y x :=
        integral_mono_measure (Measure.restrict_mono hsub le_rfl)
          (Eventually.of_forall fun x => greenFunction_nonneg isBounded_ball y x) hd.1
      _ ≤ C := hd.2
  refine ⟨hp.integral_prod_right, hp.prod_left_ae, hp.prod_right_ae, ?_, ?_⟩
  · exact integral_nonneg fun x => integral_nonneg fun y => greenFunction_nonneg hVb y x
  · rw [← integral_integral_swap hp]
    calc
      (∫ y, (∫ x in V, greenFunction V y x) ∂ν) ≤ ∫ _y, C ∂ν :=
        integral_mono_ae hp.integral_prod_left (integrable_const C) hrowV
      _ = C * (ν Set.univ).toReal := by simp [Measure.real, mul_comm]

/-- Vanishing source masses imply convergence to zero in integral norm. -/
theorem tendsto_transposedGreen_integral_norm_of_mass_tendsto_zero
    {R : ℝ} (hR : 0 < R) {V : Set ℂ} (hV : IsOpen V)
    (hsub : V ⊆ ball 0 R) (ν : ℕ → Measure ℂ) [∀ n, IsFiniteMeasure (ν n)]
    (hν : ∀ n, ∀ᵐ y ∂(ν n), y ∈ V)
    (hmass : Tendsto (fun n => (ν n Set.univ).toReal) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in V, ‖∫ y, greenFunction V y x ∂(ν n)‖) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := transposedGreen_mass_bound hR
  have hlim : Tendsto (fun n => C * (ν n Set.univ).toReal) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hmass
  apply squeeze_zero (fun n => integral_nonneg fun x => norm_nonneg _) _ hlim
  intro n
  have hn := hbound hV hsub (ν n) (hν n)
  have hVb : Bornology.IsBounded V := isBounded_ball.subset hsub
  have heq : (∫ x in V, ‖∫ y, greenFunction V y x ∂(ν n)‖) =
      ∫ x in V, ∫ y, greenFunction V y x ∂(ν n) := by
    apply integral_congr_ae
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => greenFunction_nonneg hVb y x)]
  rw [heq]
  exact hn.2.2.2.2

#print axioms disc_green_volume_row_bound
#print axioms transposedGreen_mass_bound
#print axioms tendsto_transposedGreen_integral_norm_of_mass_tendsto_zero

end HarmonicBalls
