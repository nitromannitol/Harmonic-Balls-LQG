import HarmonicBalls.Steps.Sec11.ConeUnitPositive
import HarmonicBalls.Steps.Sec11.ConeOrdinaryUniform
import HarmonicBalls.Steps.Sec11.ConeSingularUniversal
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-! # Cone-event positivity from volume growth

The smooth-shift argument uses Leonardo Bonanno's Cameron–Martin
formalization in `LatticeProb.Bonanno.LQGMetric.Field.CameronMartin`. -/

namespace HarmonicBalls
open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Full support and annular Green-potential finiteness follow from volume growth. -/
theorem exists_cone_mass_green_thresholds_of_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Q : Set ℂ) (hQ : IsCone Q) :
    ∃ n m : ℕ, 0 < n ∧ 0 < P {ω |
      (n : ℝ≥0∞)⁻¹ < μ ω (annulus 0 1 2 ∩ coneAt Q 0) ∧
      annulusGreenPotentialSup (μ ω) 0 3 6 < (m : ℝ≥0∞)} := by
  let : IsProbabilityMeasure P := hG.isProbabilityMeasure
  let A : Set Ω := {ω | μ ω (annulus 0 1 2 ∩ coneAt Q 0) ≠ 0 ∧
    annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞}
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hG hμ
  have hae : ∀ᵐ ω ∂P, ω ∈ A := by
    filter_upwards [hfull,
      ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth hgrowth hγ hγ2 hα hG hμ 3
        (show (0 : ℝ) < 6 by norm_num)] with ω hm hg
    have hm' : 0 < μ ω (annulus 0 1 2 ∩ coneAt Q 0) := by
      simpa using hQ.annulus_mass_pos_of_fullSupport (μ ω) hm 0 (r := 1) (by norm_num)
    exact ⟨hm'.ne', hg⟩
  have hpos : 0 < P A := by
    have h := measure_mono_ae (μ := P) (show (Set.univ : Set Ω) ≤ᵐ[P] A from
      hae.mono fun _ h _ => h)
    have hA : P A = 1 := by simpa using h
    rw [hA]
    exact zero_lt_one
  obtain ⟨n, m, hn, hp⟩ := exists_positive_measure_uniform_thresholds P A
    (fun ω => μ ω (annulus 0 1 2 ∩ coneAt Q 0))
    (fun ω => annulusGreenPotentialSup (μ ω) 0 3 6) hpos (fun _ h => h)
  refine ⟨n, m, hn, hp.trans_le (measure_mono ?_)⟩
  intro ω hω
  exact ⟨hω.2.1, hω.2.2⟩


/-- A fixed cone event has positive probability under volume growth. -/
theorem cone_unit_event_positive_of_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    0 < P {ω | coneMassEvent (μ ω) Q M 1 0} := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  obtain ⟨n, m, hn, hp⟩ := exists_cone_mass_green_thresholds_of_growth hgrowth hγ hγ2 hα hG hμ Q hQ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨c, hc, hheight⟩ := exists_cone_bump_height hγ (inv_pos.mpr hnR)
    (show 0 ≤ M * (m : ℝ) by positivity)
  obtain ⟨f, hf, _, _, hinner, houter⟩ := exists_cone_smooth_bump 0 (r := 1) (by norm_num) hc
  let ν : Ω → Measure ℂ := fun ω => (μ ω).withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x)))
  have hν : IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) f) ν := by
    have hw := Section6.lqgMeasureWeylScaling Ω P γ α₀ hC hcirc hG hγ hγ2 hα μ hμ
    filter_upwards [hw] with ω hω
    exact hω f hf.continuous
  have hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U :=
    lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α₀ hγ hγ2 hα Ω P hC hcirc μ hG hμ
  have hcone : annulus (0 : ℂ) 1 (2 * 1) ∩ coneAt Q 0 ⊆ ball 0 7 := by
    intro x hx
    have := hx.1.1
    change dist x 0 < 7
    change dist x 0 < 2 * 1 at this
    linarith
  have hgreen : annulus (0 : ℂ) (3 * 1) (6 * 1) ⊆ ball 0 7 := by
    intro x hx
    have := hx.1
    change dist x 0 < 7
    change dist x 0 < 6 * 1 at this
    linarith
  have hqm : MeasurableSet (annulus (0 : ℂ) 1 (2 * 1) ∩ coneAt Q 0) :=
    (measurableSet_ball.diff measurableSet_closedBall).inter
      ((Homeomorph.addRight 0).measurableEmbedding.measurableSet_image.mpr hQm)
  obtain ⟨ε, hε, hdec⟩ := hG.exists_enclosing_fixedShift_coneMassEvent_representation
    (show (0 : ℝ) < 7 by norm_num) (show (7 : ℝ) < 8 by norm_num) hf.continuous hf.contDiffOn
    μ ν hμ hν hfull Q M 1 0 hqm hcone hgreen
  obtain ⟨B, hB, hE, hEp⟩ := hdec 0
  apply cone_event_pos_of_smooth_shift hG (by linarith [hε.1]) hε.2 hf.contDiffOn 0 hB
    (fun ω => coneMassEvent (μ ω) Q M 1 0) (fun ω => coneMassEvent (ν ω) Q M 1 0) hE hEp
    {ω | (n : ℝ≥0∞)⁻¹ < μ ω (annulus 0 1 2 ∩ coneAt Q 0) ∧
      annulusGreenPotentialSup (μ ω) 0 3 6 < (m : ℝ≥0∞)} hp
  filter_upwards [] with ω hω
  apply coneMassEvent_of_bump (μ ω) Q M 1 γ c 0 f hQm hinner houter
    (C₁ := (n : ℝ≥0∞)⁻¹) (C₂ := (m : ℝ≥0∞))
    (by simpa using hω.1.le) (by simpa using hω.2.le)
  have hreal : ENNReal.ofReal (M * (m : ℝ)) ≤ ENNReal.ofReal (Real.exp (γ * c) * (n : ℝ)⁻¹) :=
    ENNReal.ofReal_le_ofReal hheight
  rw [ENNReal.ofReal_mul (Real.exp_pos _).le] at hreal
  simpa [ENNReal.ofReal_mul hM.le, ENNReal.ofReal_inv_of_pos hnR] using hreal

/-- A fixed reference law gives a common positive bound for the ordinary cone
 events at all centers and dyadic scales. -/
theorem cone_ordinary_event_uniform_positive_of_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω' : Type u} [MeasurableSpace Ω'] {P' : Measure Ω'} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (hG' : IsWholePlaneGFF P' hC' hcirc')
    (hμ' : IsLQGMeasureOfField P' γ 0 hcirc' μ')
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ (n : ℕ) (z : ℂ), p ≤ P {ω | coneMassEvent (μ ω) Q M (dyadicScale n) z} := by
  refine ⟨P' {ω | coneMassEvent (μ' ω) Q M 1 0}, ?_, ?_⟩
  · exact cone_unit_event_positive_of_growth hgrowth hγ hγ2 (by unfold lqgQ; positivity) hG' hμ' Q hQ hM
  · intro Ω _ P hC hcirc μ hG hμ n z
    exact le_of_eq (cone_ordinary_event_probability_eq_reference hγ hG hG' hμ hμ' Q hQ M n z).symm


/-- A common positive bound for singular cone events, assuming cofinal
measure existence in each singular realization. -/
theorem cone_singular_universal_measurable_witness_of_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω' : Type u} [MeasurableSpace Ω'] {P' : Measure Ω'} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (hG' : IsWholePlaneGFF P' hC' hcirc')
    (hμ' : IsLQGMeasureOfField P' γ 0 hcirc' μ')
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    ∃ p : ℝ≥0∞, 0 < p ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) →
      ∀ (n : ℕ) (z : ℂ),
      dyadicScale n / 100 ≤ infDist (0 : ℂ) (annulus z (dyadicScale n) (6 * dyadicScale n)) →
      ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M (dyadicScale n) z}, MeasurableSet A ∧ p ≤ P A := by
  let K : ℝ := ((1201 : ℝ) ^ |-(γ * α)|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨P' {ω | coneMassEvent (μ' ω) Q (M * K) 1 0}, ?_, ?_⟩
  · exact cone_unit_event_positive_of_growth hgrowth hγ hγ2 (by unfold lqgQ; positivity)
      hG' hμ' Q hQ (mul_pos hM hK)
  · intro Ω _ P hC hcirc μ hG hμ hE n z hd
    obtain ⟨ν, hν, hrepr⟩ := Section6.exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal
      P γ hγ hγ2 hC hcirc hG hE
    have hweyl : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
        ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
      filter_upwards [hrepr, hμ] with ω hω hm
      rw [hω α hα (μ ω) hm]
    obtain ⟨A, hA, hAm, hAbound⟩ := exists_cone_measurable_subset_of_singular_weight
      P (dyadicScale_pos n) hM.le hQ hd (hG.aemeasurable_lqgMeasure hμ) hweyl
    refine ⟨A, hA, hAm, ?_⟩
    rw [← cone_ordinary_event_probability_eq_reference hγ hG hG' hν hμ' Q hQ (M * K) n z]
    exact hAbound


/-- The frozen Lemma 11.8 follows from volume growth and measure existence. -/
theorem coneBadEventProbability_of_growth_and_existence
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) :
    ConeBadEventProbabilityStmt.{u} := by
  intro γ α hγ hγ2 hα Q hQ M hM
  classical
  by_cases hex : ∃ (Ω : Type u) (m : MeasurableSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, hG₀⟩ := hex
    let : MeasurableSpace Ω₀ := m₀
    have hE₀ := hE Ω₀ P₀ γ 0 hC₀ hcirc₀
    obtain ⟨μ₀, hμ₀⟩ := hE₀ hG₀ hγ hγ2 (by unfold lqgQ; positivity)
    obtain ⟨p, hp, hbound⟩ := cone_singular_universal_measurable_witness_of_growth hgrowth
      hγ hγ2 hα hG₀ hμ₀ Q hQ hM
    let q : ℝ≥0∞ := min p 1
    have hq : 0 < q := lt_min hp (by norm_num)
    have hqtop : q ≠ ∞ := ne_of_lt (lt_of_le_of_lt (min_le_right p 1) (by simp))
    have hqreal : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    let δ : ℝ := min 1 q.toReal / 2
    have hδpos : 0 < δ := by dsimp [δ]; positivity
    have hδone : δ < 1 := by dsimp [δ]; have := min_le_left (1 : ℝ) q.toReal; linarith
    have hδq : δ ≤ q.toReal := by
      dsimp [δ]; have := min_le_right (1 : ℝ) q.toReal; linarith
    have hδp : ENNReal.ofReal δ ≤ p := by
      calc
        ENNReal.ofReal δ ≤ ENNReal.ofReal q.toReal := ENNReal.ofReal_le_ofReal hδq
        _ = q := ENNReal.ofReal_toReal hqtop
        _ ≤ p := min_le_left p 1
    refine ⟨δ, ⟨hδpos, hδone⟩, ?_⟩
    intro Ω _ P hC hcirc μ hG hμ z
    refine ⟨0, ?_⟩
    intro n _ hd
    obtain ⟨A, hA, hAm, hAp⟩ := hbound P hC hcirc μ hG hμ
      (fun k => hE Ω P γ (lqgQ γ - 1 / ((k : ℝ) + 1)) hC hcirc) n z (le_of_lt hd)
    exact ⟨A, hA, hAm, hδp.trans hAp⟩
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω _ P hC hcirc μ hG
    exact (hex ⟨Ω, inferInstance, P, hC, hcirc, hG⟩).elim

#print axioms exists_cone_mass_green_thresholds_of_growth
#print axioms cone_unit_event_positive_of_growth
#print axioms cone_ordinary_event_uniform_positive_of_growth
#print axioms cone_singular_universal_measurable_witness_of_growth
#print axioms coneBadEventProbability_of_growth_and_existence
end HarmonicBalls
