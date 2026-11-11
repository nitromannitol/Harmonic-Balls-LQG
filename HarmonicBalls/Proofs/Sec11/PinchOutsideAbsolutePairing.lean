import HarmonicBalls.Proofs.Sec11.PinchOutsideRadialTests

/-! # Absolute local field pairings outside the pinch core

The circle-density approximation uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped Topology

/-- A unit-integral test outside the core has an absolute pairing version in
the outside field modulo constants, using the pinned unit-circle average. -/
theorem IsCorrectedPinchConfiguration.exists_outside_absolute_pairing
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) (ψ : ℂ → ℝ)
    (hψ : IsTestFunction (closure W)ᶜ ψ) (hψint : ∫ x, ψ x = 1) :
    ∃ X : Ω → ℝ, @Measurable Ω ℝ
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ X ∧
      X =ᵐ[P] fun ω => hC ω ψ := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (h.eventually_radialAnnularTest_outside one_pos (Or.inl rfl))
  let b (n : ℕ) := radialAnnularTest 1 one_pos (n + N)
  have hb (n : ℕ) : IsTestFunction (closure W)ᶜ (b n) := hN (n + N) (by omega)
  let φ (n : ℕ) := ψ - b n
  have hφ (n : ℕ) : IsTestFunction (closure W)ᶜ (φ n) ∧ ∫ x, φ n x = 0 := by
    have hi : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
    have hj : Integrable (b n) := (hb n).1.continuous.integrable_of_hasCompactSupport (hb n).2.1
    refine ⟨⟨hψ.1.sub (hb n).1, hψ.2.1.sub (hb n).2.1,
      (tsupport_sub _ _).trans (union_subset hψ.2.2 (hb n).2.2)⟩, ?_⟩
    change ∫ x, (ψ x - b n x) = 0
    rw [integral_sub hi hj, hψint, radialAnnularTest_integral]
    exact sub_self _
  have hp := (hgff.tendstoInMeasure_circleDensity_pairing one_pos one_pos 0).comp
    (tendsto_add_atTop_nat N)
  change TendstoInMeasure P (fun n ω => hC ω (b n)) atTop (fun ω => hcirc ω 1 0) at hp
  obtain ⟨s, hs, hsae⟩ := hp.exists_seq_tendsto_ae
  have hlin : ∀ᵐ ω ∂P, ∀ n, hC ω (φ n) = hC ω ψ - hC ω (b n) := by
    apply ae_all_iff.mpr
    intro n
    have hl := hgff.ae_pairing_linear_combination (hψ.mono_set (subset_univ _))
      ((hb n).mono_set (subset_univ _)) 1 (-1)
    filter_upwards [hl] with ω hl
    change hC ω (fun x => ψ x - b n x) = hC ω ψ - hC ω (b n)
    simpa [sub_eq_add_neg] using hl
  let X : Ω → ℝ := fun ω => liminf (fun n => hC ω (φ (s n))) atTop
  refine ⟨X, ?_, ?_⟩
  · rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    apply Measurable.liminf
    intro n
    simpa only [fieldPairing, zero_mul, sub_zero] using
      (measurable_fieldPairing_modConst 0 hC (closure W)ᶜ (φ (s n)) (hφ (s n)))
  · filter_upwards [hsae, hlin, hgff.ae_circleAverage_one_zero] with ω hω hl hpin
    have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => hC ω ψ) atTop (𝓝 (hC ω ψ))).sub hω
    have ht' : Tendsto (fun n => hC ω (φ (s n))) atTop (𝓝 (hC ω ψ)) := by
      simpa [hl, hpin] using ht
    exact ht'.liminf_eq

end HarmonicBalls
