import HarmonicBalls.Proofs.Sec11.AbsoluteMassExhaustion
import HarmonicBalls.Proofs.Sec11.PinchOutsideCircleAverage
import HarmonicBalls.Proofs.Sec6.AnnularCenteredExhaustion
import HarmonicBalls.Proofs.Sec11.PinchGreenAnnularLocality

/-! # Absolute mass of the outside Green annulus

The centered annular decoder uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem. -/

namespace HarmonicBalls
open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

/-- The absolute mass of the Green annulus has a version measurable in the
field outside the pinch core modulo constants. -/
theorem IsCorrectedPinchConfiguration.exists_outside_green_annulus_mass
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus 0 3 6)) = 0) :
    ∃ c : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ c ∧
      c =ᵐ[P] fun ω => μ ω (annulus 0 3 6) := by
  classical
  let O : Set ℂ := annulus 0 3 6
  have hO : IsOpen O := isOpen_ball.sdiff isClosed_closedBall
  have hOout : O ⊆ (closure W)ᶜ := h.green_annulus_subset_outside
  have ha : (4 : ℂ) ∈ O := by
    change dist (4 : ℂ) 0 < 6 ∧ ¬ dist (4 : ℂ) 0 ≤ 3
    norm_num [dist_eq_norm]
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO 4 ha
  have ht : Tendsto dyadicScale atTop (𝓝 0) :=
    tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hε))
  obtain ⟨F, d, hFm, hmono, hF, hbounded, hfrontF, hdm, hde⟩ :=
    Section6.IsWholePlaneGFF.exists_centered_lqg_annular_exhaustion hgff hμ 0
      (by norm_num : (0 : ℝ) ≤ 3) (by norm_num : (3 : ℝ) < 6) hfront 4 ha
  let E (n : ℕ) := if N ≤ n then F n else ∅
  have hEm (n : ℕ) : MeasurableSet (E n) := by
    by_cases hn : N ≤ n <;> simp [E, hn, hFm n]
  have hEmono : Monotone E := by
    intro i j hij
    by_cases hi : N ≤ i
    · have hj := hi.trans hij
      simpa [E, hi, hj] using hmono hij
    · simp [E, hi]
  have hEU : (⋃ n, E n) = O := by
    change (⋃ n, E n) = annulus 0 3 6
    rw [← hF]
    ext x
    simp only [mem_iUnion]
    constructor
    · rintro ⟨n, hn⟩
      by_cases hnn : N ≤ n
      · exact ⟨n, by simpa [E, hnn] using hn⟩
      · simp [E, hnn] at hn
    · rintro ⟨n, hn⟩
      exact ⟨max N n, by simpa [E, le_max_left] using hmono (le_max_right N n) hn⟩
  have hEb : Bornology.IsBounded (⋃ n, E n) := by
    rw [hEU]
    change Bornology.IsBounded (annulus 0 3 6)
    rw [← hF]
    exact hbounded
  have hEf : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 := by
    filter_upwards [hfrontF] with ω hf
    refine ⟨?_, ?_⟩
    · intro n
      by_cases hn : N ≤ n
      · simpa [E, hn] using hf.1 n
      · simp [E, hn, frontier_empty]
    · rw [hEU]
      change μ ω (frontier (annulus 0 3 6)) = 0
      rw [← hF]
      exact hf.2
  have hlocal (n : ℕ) : ∃ g : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance).prod
          inferInstance) _ (Function.uncurry g) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ E n, g ω z = fieldCircleAverage 0 (hcirc ω) (dyadicScale n) z := by
    by_cases hn : N ≤ n
    · have hδ : 0 < (ε - dyadicScale n) / 2 := by linarith [hN n hn]
      have hball : closedBall (4 : ℂ) (dyadicScale n + (ε - dyadicScale n) / 2) ⊆ O :=
        (closedBall_subset_ball (by linarith [hN n hn])).trans hεO
      obtain ⟨X, hX, hXe⟩ := h.exists_outside_circle_average hgff (dyadicScale_pos n)
        hδ 4 (hball.trans hOout)
      have hdm' : @Measurable (Ω × ℂ) ℝ
          ((MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance).prod
            inferInstance) _ (Function.uncurry (d n)) := by
        rw [← fieldSigmaAlgebraModConst_eq_comap_localModConstPairings]
        have hf : @Measurable (Ω × ℂ) Ω
            ((Section6.fieldSigmaAlgebraModConst 0 hC (closure W)ᶜ).prod inferInstance)
            (Section6.fieldSigmaAlgebraModConst 0 hC O) Prod.fst :=
          measurable_fst.mono le_rfl (fieldSigmaAlgebraModConst_mono 0 hC hOout)
        exact (hdm n).comp (hf.prodMk measurable_snd)
      refine ⟨fun ω z => d n ω z + X ω, hdm'.add (hX.comp measurable_fst), ?_⟩
      filter_upwards [hde n, hXe] with ω hd hx z hz
      have hz' : z ∈ F n := by simpa [E, hn] using hz
      rw [hd z hz', hx]
      simp [fieldCircleAverage]
    · refine ⟨fun _ _ => 0, measurable_const, ?_⟩
      filter_upwards with ω z hz
      simp [E, hn] at hz
  choose g hgm hge using hlocal
  obtain ⟨c, hcm, hce⟩ := hgff.exists_local_absolute_mass_of_exhaustion hμ
    (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance)
    E hEm hEmono hEb hEf g hgm hge
  exact ⟨c, hcm, by simpa [hEU] using hce⟩

/-- The Green-potential threshold has an outside-field version under the
standard annular continuity, finiteness and positivity assumptions. -/
theorem IsCorrectedPinchConfiguration.exists_outside_green_threshold
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus 0 3 6)) = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus 0 3 6) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 3 6)) (M : ℝ) :
    ∃ b : Ω → ℝ≥0∞, @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ b ∧
      b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6 := by
  obtain ⟨c, hc, hce⟩ := h.exists_outside_green_annulus_mass hgff hμ hfront
  exact h.exists_outside_green_of_annulus_mass hgff hμ hfront hfinite hpositive M c hc hce

/-- The annular mass decoder supplies the Green threshold in the conditional
second-pinch argument; the metric separation and interior premises remain
explicit. -/
theorem IsCorrectedPinchConfiguration.positive_second_of_outside_green_annulus
    {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {Ω : Type*} [m₀ : MeasurableSpace Ω] {P : Measure Ω}
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus 0 3 6)) = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus 0 3 6) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus 0 3 6))
    (hm : MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance ≤ m₀) (A : Set Ω) (D : Ω → ℂ → ℂ → ℝ) (hδ : 0 < δ) (M : ℝ)
    (a : Ω → ℝ≥0∞)
    (hA : MeasurableSet[MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ)
      inferInstance] A) (hAp : 0 < P A)
    (ha : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance) _ a)
    (hae : a =ᵐ[P] fun ω => ENNReal.ofReal
      (setDist (D ω) (sphere 0 δ) (sphere 0 (2 * δ))))
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (D ω) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (D ω) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) |
          MeasurableSpace.comap (localModConstPairings 0 hC (closure W)ᶜ) inferInstance]) ω) :
    0 < P {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (D ω) U V δ M} := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨b, hb, hbe⟩ := h.exists_outside_green_threshold hgff hμ hfront hfinite hpositive M
  exact positive_pinchSecondEvent_of_conditional_null_massDiameter_representatives P _ hm A D μ
    U V hδ M a b hA hAp ha hb hae hbe hmetric hgreen hinside

#print axioms IsCorrectedPinchConfiguration.positive_second_of_outside_green_annulus
#print axioms IsCorrectedPinchConfiguration.exists_outside_green_threshold
#print axioms IsCorrectedPinchConfiguration.exists_outside_green_annulus_mass
end HarmonicBalls
