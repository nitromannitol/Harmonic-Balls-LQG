import HarmonicBalls.Proofs.Sec10.HoleRemainingMassLipschitz
import HarmonicBalls.Proofs.Sec5.InteriorHausdorffContinuity
import HarmonicBalls.Proofs.Sec10.HoleExtinctionEndpoint

/-! # Continuity of remaining mass

Continuity of total cluster mass controls the mass absorbed from any fixed
finite-mass set, including after the cluster meets the unit circle.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- For nested measurable sets, the decrease in remaining mass is at most
the increase in total mass. -/
theorem remaining_measure_real_decrease_le
    (μ : Measure ℂ) {U A B : Set ℂ} (hU : μ U ≠ ∞)
    (hA : MeasurableSet A) (hAB : A ⊆ B) (hBfin : μ B ≠ ∞) :
    0 ≤ (μ (U \ A)).toReal - (μ (U \ B)).toReal ∧
      (μ (U \ A)).toReal - (μ (U \ B)).toReal ≤ (μ B).toReal - (μ A).toReal := by
  have hfinA : μ A ≠ ∞ := ne_top_of_le_ne_top hBfin (measure_mono hAB)
  have hfinD : μ (B \ A) ≠ ∞ := ne_top_of_le_ne_top hBfin (measure_mono sdiff_subset)
  have hfinU (C : Set ℂ) : μ (U \ C) ≠ ∞ :=
    ne_top_of_le_ne_top hU (measure_mono sdiff_subset)
  have hle : μ (U \ B) ≤ μ (U \ A) :=
    measure_mono (sdiff_subset_sdiff_right hAB)
  have hsplit : U \ A ⊆ (U \ B) ∪ (B \ A) := by
    intro x hx
    by_cases hxb : x ∈ B
    · exact Or.inr ⟨hxb, hx.2⟩
    · exact Or.inl ⟨hx.1, hxb⟩
  have hbound := (measure_mono (μ := μ) hsplit).trans (measure_union_le _ _)
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfinU B, hfinD⟩) hbound
  rw [ENNReal.toReal_add (hfinU B) hfinD] at hreal
  have hrealmono := ENNReal.toReal_mono (hfinU A) hle
  have hmass := measure_add_sdiff (μ := μ) hA.nullMeasurableSet B
  rw [union_eq_right.mpr hAB] at hmass
  have hmassreal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_add hfinA hfinD] at hmassreal
  constructor <;> linarith

/-- Continuity of total mass for a monotone family implies continuity of the
remaining mass of any finite-mass set. -/
theorem continuousAt_remaining_measure_of_continuous_mass
    (μ : Measure ℂ) {U : Set ℂ} (hU : μ U ≠ ∞) {C : ℝ → Set ℂ} {t : ℝ}
    (ht : 0 < t) (hopen : ∀ s, 0 < s → IsOpen (C s))
    (hmono : ∀ s r, 0 < s → s ≤ r → C s ⊆ C r)
    (hfin : ∀ s, 0 < s → μ (C s) ≠ ∞)
    (hcont : ContinuousAt (fun s => (μ (C s)).toReal) t) :
    ContinuousAt (fun s => (μ (U \ C s)).toReal) t := by
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) _
    (tendsto_iff_dist_tendsto_zero.mp hcont.tendsto)
  filter_upwards [Ioi_mem_nhds ht] with s hs
  simp only [Real.dist_eq]
  rcases le_total s t with hst | hts
  · obtain ⟨hlow, hupp⟩ := remaining_measure_real_decrease_le μ hU
      (hopen s hs).measurableSet (hmono s t hs hst) (hfin t ht)
    have hmass : (μ (C s)).toReal ≤ (μ (C t)).toReal :=
      ENNReal.toReal_mono (hfin t ht) (measure_mono (hmono s t hs hst))
    rw [abs_of_nonneg hlow, abs_of_nonpos (sub_nonpos.mpr hmass)]
    linarith
  · obtain ⟨hlow, hupp⟩ := remaining_measure_real_decrease_le μ hU
      (hopen t ht).measurableSet (hmono t s ht hts) (hfin s hs)
    have hmass : (μ (C t)).toReal ≤ (μ (C s)).toReal :=
      ENNReal.toReal_mono (hfin s hs) (measure_mono (hmono t s ht hts))
    rw [abs_of_nonpos (by linarith :
      (μ (U \ C s)).toReal - (μ (U \ C t)).toReal ≤ 0),
      abs_of_nonneg (sub_nonneg.mpr hmass)]
    linarith

universe u

/-- Under I2 and the explicit Section 6 and 8 estimates, remaining mass is
continuous at all positive times for every finite-mass set and every pole,
including after the cluster touches the unit circle. -/
theorem ae_continuousAt_cluster_remaining_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      ∀ U : Set ℂ, μ ω U ≠ ∞ →
        ContinuousAt (fun s => (μ ω (U \ cluster (μ ω) 1 z s)).toReal) t := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_continuousAt_measure_cluster hI2 (clusterOpenLaplacian_proved hI2)
      (clusterMonotone_proved hI2) (clusterConservationOfMass_proved hI2) h611 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hcont hopen hmono hmass
  intro z hz t ht U hU
  apply continuousAt_remaining_measure_of_continuous_mass (μ ω) hU ht
    (fun s hs => (hopen s 1 hs zero_lt_one z hz).1)
    (fun s r hs hsr => hmono s r 1 hs hsr zero_lt_one z hz)
    (fun s hs => ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (hmass 1 s zero_lt_one hs z hz).1)
  exact (ENNReal.tendsto_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (hmass 1 t zero_lt_one ht z hz).1)).comp (hcont z hz t ht).tendsto

/-- The remaining mass of a bounded hole decreases continuously to zero at
its lifetime endpoint, with no endpoint compact-containment hypothesis. -/
theorem ae_cluster_hole_continuous_mass_extinction
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 →
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∃ L : ℝ, t < L ∧
        (∀ s : ℝ, t ≤ s →
          (μ ω (U \ cluster (μ ω) 1 z s) = 0 ↔ L ≤ s)) ∧
        Tendsto (fun s : ℝ => (μ ω (U \ cluster (μ ω) 1 z s)).toReal)
          (𝓝 L) (𝓝 0) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_extinction_at_lifetime_endpoint hI2 h611 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_continuousAt_cluster_remaining_mass hI2 h611 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    lqgMeasureFullSupportStmt_of_volumeGrowth hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2) h611 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ]
    with ω hlife hcont hfull hmono hopen hnull hmeasure
  let : (μ ω).IsOpenPosMeasure := ⟨fun V hV hne => (hfull V hV hne).ne'⟩
  let : IsLocallyFiniteMeasure (μ ω) := hmeasure.isLocallyFiniteMeasure
  intro t ht z hz hcl U hU hUb
  obtain ⟨L, htL, hbefore, hafter, _, _⟩ := hlife t ht z hz hcl U hU hUb
  have hUfin : μ ω U ≠ ∞ :=
    ne_top_of_le_ne_top (hUb.isCompact_closure.measure_lt_top (μ := μ ω)).ne
      (measure_mono subset_closure)
  have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure
      (hcl.trans ball_subset_closedBall) hU hUb
  have heq (s : ℝ) (hts : t ≤ s) :
      μ ω (U \ cluster (μ ω) 1 z s) = 0 ↔ L ≤ s := by
    have hs := ht.trans_le hts
    rw [measure_sdiff_eq_zero_iff_no_descendant (μ ω)
      (closure_mono (hmono t s 1 ht hts zero_lt_one z hz))
      (hopen s 1 hs zero_lt_one z hz).1 hU hUdisc (hnull s hs z hz)]
    constructor
    · intro hno
      by_contra hnot
      exact hno (hbefore s hts (lt_of_not_ge hnot))
    · exact hafter s
  refine ⟨L, htL, heq, ?_⟩
  have hzero := (heq L htL.le).2 le_rfl
  simpa only [hzero, ENNReal.toReal_zero] using (hcont z hz L (ht.trans htL) U hUfin).tendsto

end HarmonicBalls
