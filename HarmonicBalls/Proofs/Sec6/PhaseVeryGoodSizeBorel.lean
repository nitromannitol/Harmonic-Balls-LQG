import HarmonicBalls.Proofs.Sec6.PhaseVeryGoodVersions
import HarmonicBalls.Proofs.Sec6.VeryGoodSizeBorel

/-! # Borel representatives for fixed phase

The imported locality development uses Leonardo Bonanno's
`LatticeProb.Prob.Birkhoff` formalization of the ergodic theorem.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter MarkovProcess
open scoped ENNReal NNReal

open MarkovProcess in
/-- A single Borel set represents the very-good-annulus event at the origin
on any class of atomless measures whose relevant annuli have finite mass and
positive mass threshold. Point avoidance is an explicit hypothesis. -/
theorem exists_measurable_phaseVeryGoodAnnulus_on_class
    (S : Set (Measure ℂ)) (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (phase : ℂ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hreg : ∀ ν ∈ S, (∀ x : ℂ, ν {x} = 0) ∧
      ∀ (n : ℕ) (j k : ℤ) (l : ℕ),
        let r := ρ * (7 : ℝ)⁻¹ ^ l
        let z := (phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
        ν (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
          0 < ENNReal.ofReal a * ν (annulus z (3 * r) (5 * r)))
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ ν ∈ S,
      (ν ∈ G ↔ PhaseVeryGoodAnnulus ν βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase) := by
  let Ω := {ν : Measure ℂ // ν ∈ S}
  let μ : Ω → Measure ℂ := Subtype.val
  have hμ : Measurable μ := measurable_subtype_coe
  let P : Measure Ω := Measure.count
  have hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), ∃ A : Set Ω, MeasurableSet A ∧ ∀ᵐ ω ∂P,
      (ω ∈ A ↔ IsGoodAnnulus (μ ω) (ρ * (7 : ℝ)⁻¹ ^ l)
        (phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b) := by
    intro n j k l
    let r := ρ * (7 : ℝ)⁻¹ ^ l
    let z := (phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
    have hr : 0 < r := mul_pos hρ (pow_pos (by norm_num) l)
    obtain ⟨G, hG, hrep⟩ := exists_measurable_isGoodAnnulus_on_atomless r hr z a b
      (annulus_smallBallHitting_of_ae_point_avoidance r hr z
        (by intro u _ x _ hxu; exact hpolar u x hxu))
    refine ⟨μ ⁻¹' G, hG.preimage hμ, Filter.Eventually.of_forall ?_⟩
    intro ω
    have hω := hreg ω.1 ω.2
    exact hrep (μ ω) ⟨hω.1⟩ (hω.2 n j k l).1 (hω.2 n j k l).2
  obtain ⟨A, hA, hrep⟩ := exists_measurable_phaseVeryGoodAnnulus_version P μ βminus ρ hρ 0 phase N₀
    a b C₁m C₁p C₂m C₂p C₃
    ((measurable_annulusBallMassSize_ratio βminus ρ 0 hρ).comp hμ).aemeasurable
    ((measurable_annulusGreenPotentialRatio_zero ρ).comp hμ).aemeasurable hgood
  obtain ⟨G, hG, hGA⟩ := MeasurableSpace.measurableSet_comap.mp hA
  refine ⟨G, hG, ?_⟩
  intro ν hν
  have h := Measure.ae_count_iff.mp hrep ⟨ν, hν⟩
  simpa only [← hGA, mem_preimage, μ] using h

open MarkovProcess in
/-- The Borel representative applies simultaneously to every locally finite,
atomless, full-support measure when the mass parameter is positive. -/
theorem exists_measurable_phaseVeryGoodAnnulus_on_fullSupport
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (phase : ℂ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ (ν : Measure ℂ),
      (∀ x : ℂ, ν {x} = 0) → IsLocallyFiniteMeasure ν →
      (∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν U) →
      (ν ∈ G ↔ PhaseVeryGoodAnnulus ν βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase) := by
  let S : Set (Measure ℂ) := {ν | (∀ x : ℂ, ν {x} = 0) ∧ IsLocallyFiniteMeasure ν ∧
    ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < ν U}
  have hreg : ∀ ν ∈ S, (∀ x : ℂ, ν {x} = 0) ∧
      ∀ (n : ℕ) (j k : ℤ) (l : ℕ),
        let r := ρ * (7 : ℝ)⁻¹ ^ l
        let z := (phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
        ν (annulus z (3 * r) (5 * r)) ≠ ∞ ∧
          0 < ENNReal.ofReal a * ν (annulus z (3 * r) (5 * r)) := by
    intro ν hν
    refine ⟨hν.1, ?_⟩
    let : IsLocallyFiniteMeasure ν := hν.2.1
    intro n j k l
    let r := ρ * (7 : ℝ)⁻¹ ^ l
    let z := (phase + ((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I))
    have hr : 0 < r := mul_pos hρ (pow_pos (by norm_num) l)
    have hnonempty : (annulus z (3 * r) (5 * r)).Nonempty := by
      refine ⟨z + (((4 * r : ℝ) : ℂ)), ?_⟩
      have hd : dist (z + (((4 * r : ℝ) : ℂ))) z = 4 * r := by
        simp [dist_eq_norm, hr.le]
      change dist (z + (((4 * r : ℝ) : ℂ))) z < 5 * r ∧
        ¬ dist (z + (((4 * r : ℝ) : ℂ))) z ≤ 3 * r
      rw [hd]
      constructor <;> linarith
    have hpos := hν.2.2 _ (isOpen_ball.sdiff isClosed_closedBall) hnonempty
    exact ⟨ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset),
      ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' hpos.ne'⟩
  obtain ⟨G, hG, hrep⟩ := exists_measurable_phaseVeryGoodAnnulus_on_class S βminus ρ hρ N₀ phase
    a b C₁m C₁p C₂m C₂p C₃ hreg hpolar
  exact ⟨G, hG, fun ν hν hloc hfull => hrep ν ⟨hν, hloc, hfull⟩⟩

/-- A Borel representative works for atomless, locally finite measures with
full support inside the size annulus, without requiring mass outside it. -/
theorem exists_measurable_phaseVeryGoodAnnulus_on_size_annulus
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ) (hN₀ : 9 ≤ N₀) (phase : ℂ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (ha : 0 < a)
    (hpolar : ∀ (u x : ℂ), x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧ ∀ μ : Measure ℂ,
      (∀ x : ℂ, μ {x} = 0) → IsLocallyFiniteMeasure μ →
      (∀ U : Set ℂ, IsOpen U → U.Nonempty → U ⊆ annulus 0 (ρ / 4) (2 * ρ) → 0 < μ U) →
      (μ ∈ G ↔ PhaseVeryGoodAnnulus μ βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃ phase) := by
  let A : Set ℂ := annulus 0 (ρ / 4) (2 * ρ)
  have hAo : IsOpen A := isOpen_ball.sdiff isClosed_closedBall
  let F : Measure ℂ → Measure ℂ := fun μ => μ.restrict A + volume.restrict Aᶜ
  have hFm : Measurable F := by
    apply Measure.measurable_of_measurable_coe
    intro U hU
    simp only [F, Measure.add_apply, Measure.restrict_apply hU]
    exact (Measure.measurable_coe (hU.inter hAo.measurableSet)).add measurable_const
  obtain ⟨H, hHm, hH⟩ := exists_measurable_phaseVeryGoodAnnulus_on_fullSupport
    βminus ρ hρ N₀ phase a b C₁m C₁p C₂m C₂p C₃ ha hpolar
  refine ⟨F ⁻¹' H, hHm.preimage hFm, ?_⟩
  intro μ hatom hloc hlocal
  let : IsLocallyFiniteMeasure μ := hloc
  have hFa : ∀ x : ℂ, F μ {x} = 0 := by
    intro x
    have h1 : μ.restrict A {x} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton x)]
      exact measure_mono_null inter_subset_left (hatom x)
    have h2 : (volume.restrict Aᶜ : Measure ℂ) {x} = 0 := by
      rw [Measure.restrict_apply (measurableSet_singleton x)]
      exact measure_mono_null inter_subset_left (measure_singleton x)
    simp only [F, Measure.add_apply, h1, h2, add_zero]
  have hFl : IsLocallyFiniteMeasure (F μ) := by
    refine ⟨fun x => ⟨ball x 1, isOpen_ball.mem_nhds (mem_ball_self (by norm_num)), ?_⟩⟩
    change (μ.restrict A + (volume.restrict Aᶜ : Measure ℂ)) (ball x 1) < ∞
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.2 ⟨
      (Measure.restrict_apply_le A _).trans_lt (lt_top_iff_ne_top.mpr measure_ball_ne_top),
      (Measure.restrict_apply_le Aᶜ _).trans_lt (lt_top_iff_ne_top.mpr measure_ball_ne_top)⟩
  have hFfull : ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < F μ U := by
    intro U hU hUne
    by_cases hUA : (U ∩ A).Nonempty
    · have hp := hlocal (U ∩ A) (hU.inter hAo) hUA inter_subset_right
      have hp' : 0 < μ.restrict A U := by
        rw [Measure.restrict_apply hU.measurableSet]
        exact hp
      change 0 < μ.restrict A U + (volume.restrict Aᶜ : Measure ℂ) U
      exact lt_of_lt_of_le hp' (le_add_of_nonneg_right (zero_le))
    · have hsub : U ⊆ Aᶜ := by
        intro x hx hxA
        exact hUA ⟨x, hx, hxA⟩
      have hp : 0 < (volume : Measure ℂ) U := hU.measure_pos volume hUne
      have hp' : 0 < (volume.restrict Aᶜ : Measure ℂ) U := by
        rw [Measure.restrict_apply hU.measurableSet, inter_eq_left.mpr hsub]
        exact hp
      change 0 < μ.restrict A U + (volume.restrict Aᶜ : Measure ℂ) U
      exact lt_of_lt_of_le hp' (le_add_of_nonneg_left (zero_le))
  have hFA : (F μ).restrict A = μ.restrict A := by
    simp only [F, Measure.restrict_add, Measure.restrict_restrict hAo.measurableSet,
      inter_self, inter_compl_self, Measure.restrict_empty, add_zero]
  change (F μ ∈ H ↔ _)
  rw [hH (F μ) hFa hFl hFfull,
    ← phaseVeryGoodAnnulus_restrict_size_annulus (F μ) βminus ρ 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ phase hρ hN₀,
    hFA, phaseVeryGoodAnnulus_restrict_size_annulus μ βminus ρ 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ phase hρ hN₀]

end HarmonicBalls.Section6
