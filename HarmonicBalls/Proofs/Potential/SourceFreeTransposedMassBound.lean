import HarmonicBalls.Proofs.Potential.FiniteSourceTransposedSourceFreeHarmonicity

/-! # Uniform bounds for source-free transposed Green potentials

The potential-theoretic infrastructure used here is due to Leonardo Bonanno.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter InnerProductSpace
open scoped Topology

/-- A single constant controls all finite sources outside the observer neighborhood. -/
theorem exists_uniform_mass_bound_transposed_green_of_source_free
    {V U L : Set ℂ} (hVb : Bornology.IsBounded V) (hU : IsOpen U)
    (hL : IsCompact L) (hLU : L ⊆ U) (hUV : U ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ν : Measure ℂ) [IsFiniteMeasure ν],
      ν Vᶜ = 0 → ν U = 0 → ∀ x ∈ L,
        |∫ y, greenFunction V y x ∂ν| ≤ C * (ν univ).toReal := by
  obtain ⟨C, hC⟩ := exists_uniform_bound_transposed_green_of_source_free
    hVb hU hL hLU (hLU.trans hUV)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro ν _ hνV hνU x hx
  have hae : ∀ᵐ y ∂ν, y ∈ V \ U := by
    rw [ae_iff]
    apply measure_mono_null (show (V \ U)ᶜ ⊆ Vᶜ ∪ U from by
      intro y hy
      by_cases hv : y ∈ V
      · right
        by_contra hu
        exact hy ⟨hv, hu⟩
      · exact Or.inl hv)
    exact measure_union_null hνV hνU
  have hb : ∀ᵐ y ∂ν, ‖greenFunction V y x‖ ≤ max C 0 := by
    filter_upwards [hae] with y hy
    simpa only [Real.norm_eq_abs] using (hC y hy x hx).trans (le_max_left C 0)
  simpa only [Real.norm_eq_abs, Measure.real] using
    (norm_integral_le_of_norm_le_const hb)

/-- Vanishing total masses give uniform convergence to zero on compact observer sets,
while each potential is harmonic on the source-free open set. -/
theorem uniform_zero_and_harmonic_transposed_green_of_mass_tendsto_zero
    {V U L : Set ℂ} (hV : IsOpen V) (hVb : Bornology.IsBounded V)
    (hU : IsOpen U) (hL : IsCompact L) (hLU : L ⊆ U) (hUV : U ⊆ V)
    (ν : ℕ → Measure ℂ) [∀ n, IsFiniteMeasure (ν n)]
    (hνV : ∀ n, ν n Vᶜ = 0) (hνU : ∀ n, ν n U = 0)
    (hmass : Tendsto (fun n => (ν n univ).toReal) atTop (𝓝 0)) :
    (∀ n, HarmonicOnNhd (fun x => ∫ y, greenFunction V y x ∂(ν n)) U) ∧
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ x ∈ L,
      |∫ y, greenFunction V y x ∂(ν n)| < ε := by
  refine ⟨fun n => harmonicOnNhd_transposed_greenIntegral_of_finite_source
    hV hVb (hνV n) hU hUV (hνU n), ?_⟩
  obtain ⟨C, _, hC⟩ := exists_uniform_mass_bound_transposed_green_of_source_free
    hVb hU hL hLU hUV
  have hlim : Tendsto (fun n => C * (ν n univ).toReal) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hmass
  intro ε hε
  filter_upwards [(tendsto_order.1 hlim).2 ε hε] with n hn x hx
  exact lt_of_le_of_lt (hC (ν n) (hνV n) (hνU n) x hx) hn


end HarmonicBalls
