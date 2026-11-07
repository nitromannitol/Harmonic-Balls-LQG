import HarmonicBalls.Proofs.Sec11.PinchOutsideRadialCircle
import HarmonicBalls.Proofs.Sec6.AnnularCircleDensity

/-! # Local circle averages from the outside field

The circle-density approximation uses Leonardo Bonanno's
`LatticeProb.Bonanno.LQGMetric.Field.CameronMartin` formalization. -/

namespace HarmonicBalls
open MeasureTheory Set Metric Filter
open scoped Topology

/-- A circle with a closed ball buffered outside the core has an absolute
outside-field measurable version, anchored by the pinned radius-four circle. -/
theorem IsCorrectedPinchConfiguration.exists_outside_circle_average
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (z : ℂ) (hz : closedBall z (r + η) ⊆ (closure W)ᶜ) :
    ∃ X : Ω → ℝ, @Measurable Ω ℝ
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ X ∧
      X =ᵐ[P] fun ω => hcirc ω r z := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨R, hR, hRe⟩ := h.exists_outside_pinned_reference_circle hgff
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (h.eventually_radialAnnularTest_outside (by norm_num : (0 : ℝ) < 4) (Or.inr rfl))
  let a (n : ℕ) : ℂ → ℝ := fun x =>
    (∫ y, circleDensity r (circleDensityWidth r η (n + N))
      (circleDensityWidth_pos hr hη (n + N)) 0 y)⁻¹ *
    circleDensity r (circleDensityWidth r η (n + N))
      (circleDensityWidth_pos hr hη (n + N)) z x
  let b (n : ℕ) := radialAnnularTest 4 (by norm_num) (n + N)
  have ha (n : ℕ) : IsTestFunction (closure W)ᶜ (a n) := by
    have hw : circleDensityWidth r η (n + N) ≤ r * η := by
      unfold circleDensityWidth
      apply div_le_self (mul_nonneg hr.le hη.le)
      exact le_add_of_nonneg_left (Nat.cast_nonneg _)
    have ht := circleDensity_isTestFunction hr (circleDensityWidth_pos hr hη (n + N)) hw z _ hz
    exact ⟨contDiff_const.mul ht.1, ht.2.1.mul_left, tsupport_mul_subset_right.trans ht.2.2⟩
  have hb (n : ℕ) : IsTestFunction (closure W)ᶜ (b n) := hN (n + N) (by omega)
  let ψ (n : ℕ) := a n - b n
  have hψ (n : ℕ) : IsTestFunction (closure W)ᶜ (ψ n) ∧ ∫ x, ψ n x = 0 := by
    have hia : Integrable (a n) := (ha n).1.continuous.integrable_of_hasCompactSupport (ha n).2.1
    have hib : Integrable (b n) := (hb n).1.continuous.integrable_of_hasCompactSupport (hb n).2.1
    refine ⟨⟨(ha n).1.sub (hb n).1, (ha n).2.1.sub (hb n).2.1,
      (tsupport_sub _ _).trans (union_subset (ha n).2.2 (hb n).2.2)⟩, ?_⟩
    change ∫ x, (a n x - b n x) = 0
    rw [integral_sub hia hib, circleDensity_normalized_integral hr.le, radialAnnularTest_integral]
    exact sub_self _
  have hp := (hgff.tendstoInMeasure_circleDensity_pairing hr hη z).comp (tendsto_add_atTop_nat N)
  change TendstoInMeasure P (fun n ω => hC ω (a n)) atTop (fun ω => hcirc ω r z) at hp
  obtain ⟨s, hs, hsae⟩ := hp.exists_seq_tendsto_ae
  have hq := (hgff.tendstoInMeasure_circleDensity_pairing (by norm_num : (0 : ℝ) < 4) one_pos 0).comp
    (tendsto_add_atTop_nat N)
  change TendstoInMeasure P (fun n ω => hC ω (b n)) atTop (fun ω => hcirc ω 4 0) at hq
  obtain ⟨t, ht, htae⟩ := (hq.comp hs.tendsto_atTop).exists_seq_tendsto_ae
  let k := s ∘ t
  have hlin : ∀ᵐ ω ∂P, ∀ n, hC ω (ψ n) = hC ω (a n) - hC ω (b n) := by
    apply ae_all_iff.mpr
    intro n
    have hl := hgff.ae_pairing_linear_combination ((ha n).mono_set (subset_univ _))
      ((hb n).mono_set (subset_univ _)) 1 (-1)
    filter_upwards [hl] with ω hω
    change hC ω (fun x => a n x - b n x) = hC ω (a n) - hC ω (b n)
    simpa [sub_eq_add_neg] using hω
  let D : Ω → ℝ := fun ω => liminf (fun n => hC ω (ψ (k n))) atTop
  have hD : @Measurable Ω ℝ
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ D := by
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    apply Measurable.liminf
    intro n
    simpa only [fieldPairing, zero_mul, sub_zero] using
      (measurable_fieldPairing_modConst 0 hC (closure W)ᶜ (ψ (k n)) (hψ (k n)))
  refine ⟨fun ω => D ω + R ω, hD.add hR, ?_⟩
  filter_upwards [hsae, htae, hlin, hRe] with ω hω hω' hl hRω
  have hlim := (hω.comp ht.tendsto_atTop).sub hω'
  have hlim' : Tendsto (fun n => hC ω (ψ (k n))) atTop
      (𝓝 (hcirc ω r z - hcirc ω 4 0)) := by
    simpa [k, Function.comp_def, hl] using hlim
  dsimp [D]
  rw [hlim'.liminf_eq, hRω]
  ring

/-- The local absolute circle averages admit a jointly measurable version on
an open outside region, provided the reference circle has an outside buffer. -/
theorem IsCorrectedPinchConfiguration.exists_joint_outside_circle_average
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hgff : IsWholePlaneGFF P hC hcirc) {r η : ℝ} (hr : 0 < r) (hη : 0 < η)
    (O : Set ℂ) (hO : IsOpen O) (hOout : O ⊆ (closure W)ᶜ)
    (a : ℂ) (ha : closedBall a (r + η) ⊆ O) :
    ∃ d : Ω → ℂ → ℝ, @Measurable (Ω × ℂ) ℝ
      ((MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance).prod
        inferInstance) _ (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z r ⊆ O → d ω z = hcirc ω r z := by
  have ha' : closedBall a r ⊆ O :=
    (closedBall_subset_closedBall (by linarith)).trans ha
  obtain ⟨X, hX, hXe⟩ := h.exists_outside_circle_average hgff hr hη a (ha.trans hOout)
  obtain ⟨d, hdm, hde⟩ := hgff.exists_joint_annular_centered_circle_version
    (α₀ := 0) hr O hO a ha'
  have hdm' : @Measurable (Ω × ℂ) ℝ
      ((MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance).prod
        inferInstance) _ (Function.uncurry d) := by
    rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
    have hf : @Measurable (Ω × ℂ) Ω
        ((Section6.fieldSigmaAlgebraModConst 0 hC (closure W)ᶜ).prod inferInstance)
        (Section6.fieldSigmaAlgebraModConst 0 hC O) Prod.fst :=
      measurable_fst.mono le_rfl (fieldSigmaAlgebraModConst_mono 0 hC hOout)
    exact hdm.comp (hf.prodMk measurable_snd)
  refine ⟨fun ω z => d ω z + X ω, hdm'.add (hX.comp measurable_fst), ?_⟩
  filter_upwards [hde, hXe] with ω hd hx z hz
  rw [hd z hz, hx]
  simp [fieldCircleAverage]

#print axioms IsCorrectedPinchConfiguration.exists_joint_outside_circle_average
#print axioms IsCorrectedPinchConfiguration.exists_outside_circle_average
end HarmonicBalls
