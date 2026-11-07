import HarmonicBalls.Proofs.Sec11.PinchOutsideRadialTests

/-! # The pinned reference circle from the outside field

The circle-density pairing approximation uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization.
-/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped Topology

/-- The pinned circle average at radius four has an almost-sure version
measurable in the field outside the pinch core modulo additive constants. -/
theorem IsCorrectedPinchConfiguration.exists_outside_pinned_reference_circle
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) :
    ∃ X : Ω → ℝ, @Measurable Ω ℝ
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ X ∧
      X =ᵐ[P] fun ω => hcirc ω 4 0 := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  have hlocal := (h.eventually_radialAnnularTest_outside (by norm_num : (0 : ℝ) < 4)
    (Or.inr rfl)).and (h.eventually_radialAnnularTest_outside one_pos (Or.inl rfl))
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlocal
  let a (n : ℕ) := radialAnnularTest 4 (by norm_num) (n + N)
  let b (n : ℕ) := radialAnnularTest 1 one_pos (n + N)
  have ha (n : ℕ) : IsTestFunction (closure W)ᶜ (a n) := (hN (n + N) (by omega)).1
  have hb (n : ℕ) : IsTestFunction (closure W)ᶜ (b n) := (hN (n + N) (by omega)).2
  let ψ (n : ℕ) : ℂ → ℝ := a n - b n
  have hψ (n : ℕ) : IsTestFunction (closure W)ᶜ (ψ n) ∧ ∫ x, ψ n x = 0 := by
    have hia : Integrable (a n) := (ha n).1.continuous.integrable_of_hasCompactSupport (ha n).2.1
    have hib : Integrable (b n) := (hb n).1.continuous.integrable_of_hasCompactSupport (hb n).2.1
    refine ⟨⟨(ha n).1.sub (hb n).1, (ha n).2.1.sub (hb n).2.1,
      (tsupport_sub _ _).trans (union_subset (ha n).2.2 (hb n).2.2)⟩, ?_⟩
    change ∫ x, (a n x - b n x) = 0
    rw [integral_sub hia hib, radialAnnularTest_integral, radialAnnularTest_integral]
    exact sub_self _
  have hp := hgff.tendstoInMeasure_circleDensity_pairing (by norm_num : (0 : ℝ) < 4) one_pos 0
  change TendstoInMeasure P (fun n ω => hC ω (radialAnnularTest 4 (by norm_num) n))
    atTop (fun ω => hcirc ω 4 0) at hp
  have hp' := hp.comp (tendsto_add_atTop_nat N)
  change TendstoInMeasure P (fun n ω => hC ω (a n)) atTop (fun ω => hcirc ω 4 0) at hp'
  obtain ⟨s, hs, hsae⟩ := hp'.exists_seq_tendsto_ae
  have hq := hgff.tendstoInMeasure_circleDensity_pairing one_pos one_pos 0
  change TendstoInMeasure P (fun n ω => hC ω (radialAnnularTest 1 one_pos n))
    atTop (fun ω => hcirc ω 1 0) at hq
  have hq' := (hq.comp (tendsto_add_atTop_nat N)).comp hs.tendsto_atTop
  change TendstoInMeasure P (fun n ω => hC ω (b (s n))) atTop (fun ω => hcirc ω 1 0) at hq'
  obtain ⟨t, ht, htae⟩ := hq'.exists_seq_tendsto_ae
  let k := s ∘ t
  have hlin : ∀ᵐ ω ∂P, ∀ n, hC ω (ψ n) = hC ω (a n) - hC ω (b n) := by
    apply ae_all_iff.mpr
    intro n
    have hl := hgff.ae_pairing_linear_combination ((ha n).mono_set (subset_univ _))
      ((hb n).mono_set (subset_univ _)) 1 (-1)
    filter_upwards [hl] with ω hω
    change hC ω (fun x => a n x - b n x) = hC ω (a n) - hC ω (b n)
    simpa [sub_eq_add_neg] using hω
  let X : Ω → ℝ := fun ω => liminf (fun n => hC ω (ψ (k n))) atTop
  refine ⟨X, ?_, ?_⟩
  · rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    apply Measurable.liminf
    intro n
    simpa only [fieldPairing, zero_mul, sub_zero] using
      (measurable_fieldPairing_modConst 0 hC (closure W)ᶜ (ψ (k n)) (hψ (k n)))
  · filter_upwards [hsae, htae, hlin, hgff.ae_circleAverage_one_zero] with ω hω hω' hl hp0
    have hlim := (hω.comp ht.tendsto_atTop).sub hω'
    have hlim' : Tendsto (fun n => hC ω (ψ (k n))) atTop (𝓝 (hcirc ω 4 0)) := by
      simpa [k, Function.comp_def, hl, hp0] using hlim
    exact hlim'.liminf_eq

#print axioms IsCorrectedPinchConfiguration.exists_outside_pinned_reference_circle
end HarmonicBalls
