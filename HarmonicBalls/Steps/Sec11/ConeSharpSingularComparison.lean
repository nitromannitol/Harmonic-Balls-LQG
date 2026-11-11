import HarmonicBalls.Steps.Sec11.ConeSingularComparison
import HarmonicBalls.Steps.Sec11.ConeSingularUniversal
import HarmonicBalls.Steps.Sec11.ConeProbabilityFromLiterature

/-! # Sharp singular-weight comparison for separated annuli

The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The infimum of the singular weight yields the single oscillation factor
in the corrected proof of Lemma 11.8. -/
theorem cone_annulus_comparable_of_singular_weight_sharp
    {μ ν : Measure ℂ} {r e : ℝ} {z : ℂ}
    (hr : 0 < r) (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    ∃ c : ℝ≥0∞, Section6.IsComparableOnWith μ ν (annulus z r (6 * r)) c
      (ENNReal.ofReal ((1201 : ℝ) ^ |e|)) := by
  let B := annulus z r (6 * r)
  let f : ℂ → ℝ := fun x => ‖x‖ ^ e
  let t : ℝ := (1201 : ℝ) ^ |e|
  have ht : 0 < t := Real.rpow_pos_of_pos (by norm_num) _
  have hne : B.Nonempty := by
    refine ⟨z + ((2 * r : ℝ) : ℂ), ?_⟩
    have hdist : dist (z + ((2 * r : ℝ) : ℂ)) z = 2 * r := by
      simp [dist_eq_norm, hr.le]
    change dist (z + ((2 * r : ℝ) : ℂ)) z < 6 * r ∧
      ¬ dist (z + ((2 * r : ℝ) : ℂ)) z ≤ r
    rw [hdist]
    constructor <;> linarith
  obtain ⟨p, hp⟩ := hne
  have hp0 : 0 < ‖p‖ := (norm_le_of_mem_cone_annulus hr hd hp hp).1
  have hfp : 0 < f p := Real.rpow_pos_of_pos hp0 e
  have hlower : ∀ x ∈ B, f p / t ≤ f x := by
    intro x hx
    apply (div_le_iff₀ ht).2
    simpa [f, t, mul_comm] using rpow_norm_le_of_mem_cone_annulus (e := e) hr hd hp hx
  have hbdd : BddBelow (f '' B) := ⟨f p / t, by rintro _ ⟨x, hx, rfl⟩; exact hlower x hx⟩
  have hfne : (f '' B).Nonempty := ⟨f p, p, hp, rfl⟩
  let a : ℝ := sInf (f '' B)
  have hap : 0 < a := lt_of_lt_of_le (div_pos hfp ht) <|
    le_csInf hfne (by rintro _ ⟨x, hx, rfl⟩; exact hlower x hx)
  have halower (x : ℂ) (hx : x ∈ B) : a ≤ f x := csInf_le hbdd ⟨x, hx, rfl⟩
  have haupper (x : ℂ) (hx : x ∈ B) : f x ≤ t * a := by
    have h : f x / t ≤ a := by
      apply le_csInf hfne
      rintro _ ⟨y, hy, rfl⟩
      apply (div_le_iff₀ ht).2
      simpa [f, t, mul_comm] using rpow_norm_le_of_mem_cone_annulus (e := e) hr hd hx hy
    simpa only [mul_comm] using (div_le_iff₀ ht).1 h
  have hsub : B ⊆ ({0} : Set ℂ)ᶜ := by
    intro x hx h0
    have hx0 := (norm_le_of_mem_cone_annulus hr hd hx hp).1
    have : x = 0 := by simpa using h0
    simp [this] at hx0
  have hrestrict : μ.restrict B = (ν.withDensity fun x => ENNReal.ofReal (f x)).restrict B := by
    rw [← Measure.restrict_restrict_of_subset hsub, hμ, Measure.restrict_restrict_of_subset hsub]
  refine ⟨ENNReal.ofReal a, Section6.isComparableOnWith_of_withDensity
    (isOpen_ball.measurableSet.diff isClosed_closedBall.measurableSet)
    hrestrict (ENNReal.ofReal_ne_zero_iff.2 hap) ENNReal.ofReal_ne_top
    (ENNReal.ofReal_ne_zero_iff.2 ht) ENNReal.ofReal_ne_top ?_⟩
  intro x hx
  constructor
  · exact ENNReal.ofReal_le_ofReal (halower x hx)
  · rw [← ENNReal.ofReal_mul ht.le]
    exact ENNReal.ofReal_le_ofReal (haupper x hx)

/-- The ordinary cone event with the single distortion factor implies the
cone event for the singularly weighted measure. -/
theorem coneMassEvent_of_singular_weight_sharp
    {μ ν : Measure ℂ} {r e M : ℝ} {z : ℂ} {Q : Set ℂ}
    (hr : 0 < r) (hM : 0 ≤ M)
    (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hμ : μ.restrict {0}ᶜ = (ν.withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ)
    (hevent : coneMassEvent ν Q (M * (1201 : ℝ) ^ |e|) r z) :
    coneMassEvent μ Q M r z := by
  obtain ⟨c, hc⟩ := cone_annulus_comparable_of_singular_weight_sharp hr hd hμ
  apply coneMassEvent_of_comparableWith hc ?_ ?_ ?_ hevent
  · intro x hx
    have hx1 : dist x z < 2 * r := hx.1.1
    have hx2 : ¬ dist x z ≤ r := hx.1.2
    constructor <;> simp only [mem_ball, mem_closedBall] at * <;> linarith
  · intro x hx
    have hx1 : dist x z < 6 * r := hx.1
    have hx2 : ¬ dist x z ≤ 3 * r := hx.2
    constructor <;> simp only [mem_ball, mem_closedBall] at * <;> linarith
  · rw [ENNReal.ofReal_mul hM]

/-- A measurable inner witness retains the sharp singular-weight threshold. -/
theorem exists_cone_measurable_subset_of_singular_weight_sharp
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {μ ν : Ω → Measure ℂ} {r e M : ℝ} {z : ℂ} {Q : Set ℂ}
    (hr : 0 < r) (hM : 0 ≤ M) (hQ : IsCone Q)
    (hd : r / 100 ≤ infDist (0 : ℂ) (annulus z r (6 * r)))
    (hμ : AEMeasurable μ P)
    (hweyl : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ) :
    ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M r z}, MeasurableSet A ∧
      P {ω | coneMassEvent (ν ω) Q (M * (1201 : ℝ) ^ |e|) r z} ≤ P A := by
  have hQm : MeasurableSet Q := by
    rcases hQ with h | h
    · exact h.2.1.measurableSet
    · simpa using h.2.1.measurableSet.compl
  have hqm : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z) :=
    (measurableSet_ball.diff measurableSet_closedBall).inter
      ((Homeomorph.addRight z).measurableEmbedding.measurableSet_image.mpr hQm)
  have hn : NullMeasurableSet {ω | coneMassEvent (μ ω) Q M r z} P :=
    hμ.nullMeasurableSet_preimage (measurableSet_coneMassEvent Q M r z hqm)
  obtain ⟨A, hsub, hAm, hAeq⟩ := hn.exists_measurable_subset_ae_eq
  refine ⟨A, hsub, hAm, ?_⟩
  rw [measure_congr hAeq]
  apply measure_mono_ae
  filter_upwards [hweyl] with ω hω hevent
  exact coneMassEvent_of_singular_weight_sharp hr hM hd hω hevent

/-- The reference ordinary event at the sharp threshold bounds every
separated dyadic singular event from below, with a measurable inner witness. -/
theorem cone_singular_universal_measurable_witness_sharp
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω' : Type u} [MeasurableSpace Ω'] {P' : Measure Ω'} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ} {μ' : Ω' → Measure ℂ}
    (hG' : IsWholePlaneGFF P' hC' hcirc') (hE' : LQGMeasureExistence P' γ 0 hC' hcirc')
    (hμ' : IsLQGMeasureOfField P' γ 0 hcirc' μ')
    (Q : Set ℂ) (hQ : IsCone Q) {M : ℝ} (hM : 0 < M) :
    0 < P' {ω | coneMassEvent (μ' ω) Q (M * (1201 : ℝ) ^ |γ * α|) 1 0} ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      (∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc) →
      ∀ (n : ℕ) (z : ℂ),
      dyadicScale n / 100 ≤ infDist (0 : ℂ) (annulus z (dyadicScale n) (6 * dyadicScale n)) →
      ∃ A ⊆ {ω | coneMassEvent (μ ω) Q M (dyadicScale n) z}, MeasurableSet A ∧
        P' {ω | coneMassEvent (μ' ω) Q (M * (1201 : ℝ) ^ |γ * α|) 1 0} ≤ P A := by
  let K : ℝ := (1201 : ℝ) ^ |γ * α|
  have hK : 0 < K := Real.rpow_pos_of_pos (by norm_num) _
  constructor
  · exact cone_unit_event_positive hS hgrowth hγ hγ2 (by unfold lqgQ; positivity)
      hG' hE' hμ' Q hQ (mul_pos hM hK)
  · intro Ω _ P hC hcirc μ hG hμ hE n z hd
    obtain ⟨ν, hν, hrepr⟩ := Section6.exists_ae_all_subcritical_limits_eq_singularWeight_of_cofinal
      P γ hγ hγ2 hC hcirc hG hE
    have hweyl : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
        ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ (-(γ * α)))).restrict {0}ᶜ := by
      filter_upwards [hrepr, hμ] with ω hω hm
      rw [hω α hα (μ ω) hm]
    obtain ⟨A, hA, hAm, hAbound⟩ := exists_cone_measurable_subset_of_singular_weight_sharp
      P (dyadicScale_pos n) hM.le hQ hd (hG.aemeasurable_lqgMeasure hμ) hweyl
    refine ⟨A, hA, hAm, ?_⟩
    rw [← cone_ordinary_event_probability_eq_reference hγ hG hG' hν hμ' Q hQ (M * K) n z]
    simpa only [K, abs_neg] using hAbound

/-- The frozen Lemma 11.8 follows through the sharp singular-weight bound,
under the existing scaled-ball, volume-growth and existence hypotheses. -/
theorem coneBadEventProbability_of_existence_sharp
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
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
    obtain ⟨hp, hbound⟩ := cone_singular_universal_measurable_witness_sharp hS hgrowth
      hγ hγ2 hα hG₀ hE₀ hμ₀ Q hQ hM
    let p := P₀ {ω | coneMassEvent (μ₀ ω) Q (M * (1201 : ℝ) ^ |γ * α|) 1 0}
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

/-- Lemma 11.8 by the sharp comparison, under the same three staged
literature inputs as the existing conditional closure. -/
theorem coneBadEventProbability_of_literature_sharp
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) : ConeBadEventProbabilityStmt.{u} := by
  have hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc :=
    fun _ _ P hC hcirc => wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hS : WholePlaneScaledBallMassStep.{u} :=
    wholePlaneScaledBallMassStep_of_rescaled
      (rescaledBallMassUniformStep_of_DG hDG hAff hCC wholePlaneGFFMixtureStep_holds)
  have hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureWeylScaling P γ 0 hC hcirc :=
    fun Ω _ P γ hC hcirc => Section6.lqgMeasureWeylScaling Ω P γ 0 hC hcirc
  have hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureNonatomic P γ α hC hcirc :=
    fun Ω _ P γ α hC hcirc => Section6.lqgMeasureNonatomic_of_existence hS P γ α hC hcirc
      (fun β => hE Ω P γ β hC hcirc)
  have hgrowth : LQGVolumeGrowthAllScalesStmt.{u} :=
    lqgVolumeGrowthAllScalesStmt_of_scaled hS hW
      (fun Ω _ P γ hC hcirc => hE Ω P γ 0 hC hcirc) hN
  exact coneBadEventProbability_of_existence_sharp hS hgrowth hE


end HarmonicBalls
