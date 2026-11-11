import HarmonicBalls.Proofs.GFF.FixedShiftCircleLQGRepresentation
import HarmonicBalls.Steps.Sec11.PinchLocalData
import HarmonicBalls.Steps.Sec11.PinchGreenMeasurable
import HarmonicBalls.Proofs.Sec8.RootedContinuitySets
import HarmonicBalls.Proofs.Sec6.LQGWeylScaling
import HarmonicBalls.Proofs.Sec6.JointSingularMeasureMeasurability

/-! # Local cone mass observables

The imported fixed-shift decoder uses Leonardo Bonanno's LatticeProb
formalization. The extended Green kernel retains its infinite diagonal.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The cone mass event depends only on the restriction to any measurable set
containing both the cone annulus and the Green-potential annulus. -/
theorem coneMassEvent_iff_of_restrict_eq
    {μ ν : Measure ℂ} {U Q : Set ℂ} (M r : ℝ) (z : ℂ)
    (hU : MeasurableSet U)
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ U)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ U)
    (hlocal : μ.restrict U = ν.restrict U) :
    coneMassEvent μ Q M r z ↔ coneMassEvent ν Q M r z := by
  have hg : μ.restrict (annulus z (3 * r) (6 * r)) =
      ν.restrict (annulus z (3 * r) (6 * r)) := by
    rw [← Measure.restrict_restrict_of_subset hgreen, hlocal,
      Measure.restrict_restrict_of_subset hgreen]
  have hm : μ (annulus z r (2 * r) ∩ coneAt Q z) =
      ν (annulus z r (2 * r) ∩ coneAt Q z) := by
    have h := congrArg (fun m : Measure ℂ => m (annulus z r (2 * r) ∩ coneAt Q z)) hlocal
    simpa only [Measure.restrict_apply' hU, inter_eq_self_of_subset_left hcone] using h
  simp only [coneMassEvent, annulusGreenPotentialSup_eq_of_restrict_eq z _ _ hg, hm]

/-- The cone mass event is measurable as a function of the measure when the
cone annulus is Borel. -/
theorem measurableSet_coneMassEvent (Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z)) :
    MeasurableSet {μ : Measure ℂ | coneMassEvent μ Q M r z} := by
  exact measurableSet_le (measurable_const.mul (measurable_annulusGreenPotentialSup z _ _))
    (Measure.measurable_coe hQ)

/-- A normalized local restriction encodes the original event when the
reference mass is positive and finite. -/
theorem coneMassEvent_normalizedRestriction_iff
    (μ : Measure ℂ) {U Q : Set ℂ} (M r : ℝ) (z : ℂ)
    (hU : MeasurableSet U)
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ U)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ U)
    (hzero : μ U ≠ 0) (htop : μ U ≠ ∞) :
    coneMassEvent (normalizedRestriction μ U) Q M r z ↔ coneMassEvent μ Q M r z := by
  have hlocal : (normalizedRestriction μ U).restrict U = ((μ U)⁻¹ • μ).restrict U := by
    rw [normalizedRestriction, Measure.restrict_smul,
      Measure.restrict_restrict_of_subset (Subset.refl U), Measure.restrict_smul]
  exact (coneMassEvent_iff_of_restrict_eq M r z hU hcone hgreen hlocal).trans
    (coneMassEvent_smul_iff μ Q M r z (ENNReal.inv_ne_zero.mpr htop)
      (ENNReal.inv_ne_top.mpr hzero))

/-- Any prescribed nonempty radius interval contains a deterministic ball
whose boundary is null for both locally finite random measures. -/
theorem exists_common_continuity_ball
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ ν : Ω → Measure ℂ) (hμ : AEMeasurable μ P) (hν : AEMeasurable ν P)
    (hlμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hlν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω))
    {a b : ℝ} (hab : a < b) :
    ∃ ε ∈ Ioo a b, (∀ᵐ ω ∂P, μ ω (frontier (ball (0 : ℂ) ε)) = 0) ∧
      ∀ᵐ ω ∂P, ν ω (frontier (ball (0 : ℂ) ε)) = 0 := by
  let ρ : Ω → Measure ℂ := fun ω => μ ω + ν ω
  have hρ : AEMeasurable ρ P := hμ.add hν
  have hlρ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ρ ω) := by
    filter_upwards [hlμ, hlν] with ω hμω hνω
    let : IsLocallyFiniteMeasure (μ ω) := hμω
    let : IsLocallyFiniteMeasure (ν ω) := hνω
    constructor
    intro x
    refine ⟨ball x 1, isOpen_ball.mem_nhds (mem_ball_self (by norm_num)), ?_⟩
    simp only [ρ, Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_ball_lt_top, measure_ball_lt_top⟩
  obtain ⟨r, hr, hnull⟩ := exists_ae_null_frontier_balls_of_ae_locallyFinite P ρ hρ hlρ
    (fun _ => 0) (fun _ => a) (fun _ => b) (fun _ => hab)
  refine ⟨r 0, hr 0, ?_, ?_⟩
  · filter_upwards [hnull] with ω hω
    have h := hω 0
    simpa only [ρ, Measure.add_apply, add_eq_zero] using (show
      μ ω (frontier (ball (0 : ℂ) (r 0))) = 0 ∧
        ν ω (frontier (ball (0 : ℂ) (r 0))) = 0 by
          simpa only [ρ, Measure.add_apply, add_eq_zero] using h).1
  · filter_upwards [hnull] with ω hω
    have h := hω 0
    exact (show μ ω (frontier (ball (0 : ℂ) (r 0))) = 0 ∧
        ν ω (frontier (ball (0 : ℂ) (r 0))) = 0 by
          simpa only [ρ, Measure.add_apply, add_eq_zero] using h).2


/-- Two locally finite random measures admit one generating continuity
pi-system and one buffered exhaustion of a common continuity ball. -/
theorem exists_common_buffered_continuity_system
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ ν : Ω → Measure ℂ) (hμ : AEMeasurable μ P) (hν : AEMeasurable ν P)
    (hlμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (hlν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω)) {ε : ℝ} (hε : 0 < ε)
    (hfμ : ∀ᵐ ω ∂P, μ ω (frontier (ball (0 : ℂ) ε)) = 0)
    (hfν : ∀ᵐ ω ∂P, ν ω (frontier (ball (0 : ℂ) ε)) = 0) :
    ∃ S : Set (Set ℂ), S.Countable ∧ IsPiSystem S ∧ univ ∈ S ∧
      (∀ A ∈ S, IsOpen A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S ∧
      ∃ V : ℕ → Set ℂ, (∀ n, MeasurableSet (V n)) ∧ Monotone V ∧
        (⋃ n, V n) = ball 0 ε ∧
        (∀ n z, z ∈ V n → closedBall z (dyadicScale n) ⊆ ball 0 ε) ∧
        (∀ᵐ ω ∂P, ∀ A ∈ S, (∀ n, μ ω (frontier (V n)) = 0 ∧
          μ ω (frontier (A ∩ V n)) = 0) ∧ μ ω (frontier (⋃ n, V n)) = 0 ∧
          μ ω (frontier (A ∩ ⋃ n, V n)) = 0) ∧
        ∀ᵐ ω ∂P, ∀ A ∈ S, (∀ n, ν ω (frontier (V n)) = 0 ∧
          ν ω (frontier (A ∩ V n)) = 0) ∧ ν ω (frontier (⋃ n, V n)) = 0 ∧
          ν ω (frontier (A ∩ ⋃ n, V n)) = 0 := by
  let ρ : Ω → Measure ℂ := fun ω => μ ω + ν ω
  have hρ : AEMeasurable ρ P := hμ.add hν
  have hlρ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ρ ω) := by
    filter_upwards [hlμ, hlν] with ω hμω hνω
    let : IsLocallyFiniteMeasure (μ ω) := hμω
    let : IsLocallyFiniteMeasure (ν ω) := hνω
    constructor
    intro x
    refine ⟨ball x 1, isOpen_ball.mem_nhds (mem_ball_self (by norm_num)), ?_⟩
    simp only [ρ, Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨measure_ball_lt_top, measure_ball_lt_top⟩
  have hfρ : ∀ᵐ ω ∂P, ρ ω (frontier (ball (0 : ℂ) ε)) = 0 := by
    filter_upwards [hfμ, hfν] with ω hμω hνω
    simp [ρ, hμω, hνω]
  obtain ⟨S, hc, hp, hu, ho, hg, hs⟩ :=
    exists_ae_continuity_piSystem_of_ae_locallyFinite P ρ hρ hlρ
  obtain ⟨V, hm, hmono, hunion, hbuffer, hv⟩ :=
    exists_buffered_ball_exhaustion_of_ae_locallyFinite P ρ hρ hlρ hε hfρ
  have hfront := ae_frontiers_intersections_of_common_continuity P ρ V S hv hs
  refine ⟨S, hc, hp, hu, ho, hg, V, hm, hmono, hunion, hbuffer, ?_, ?_⟩
  · filter_upwards [hfront] with ω hω A hA
    have h := hω A hA
    simp only [ρ, Measure.add_apply, add_eq_zero] at h
    exact ⟨fun n => ⟨(h.1 n).1.1, (h.1 n).2.1⟩, h.2.1.1, h.2.2.1⟩
  · filter_upwards [hfront] with ω hω A hA
    have h := hω A hA
    simp only [ρ, Measure.add_apply, add_eq_zero] at h
    exact ⟨fun n => ⟨(h.1 n).1.2, (h.1 n).2.2⟩, h.2.1.2, h.2.2.2⟩


/-- The cone event on normalized restrictions is encoded by the real masses
on any generating pi-system. The set is obtained from measurability of the
actual event and the generating masses. -/
theorem exists_coneMassEvent_countable_encoding
    (S : Set (Set ℂ)) (hgen : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom S) (hpi : IsPiSystem S)
    (huniv : univ ∈ S)
    (Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z)) :
    ∃ C : Set (S → ℝ), MeasurableSet C ∧ ∀ μ : Measure ℂ, ∀ U : Set ℂ,
      (coneMassEvent (normalizedRestriction μ U) Q M r z ↔
        (fun i : S => (normalizedRestriction μ U i.1).toReal) ∈ C) := by
  let F := {η : Measure ℂ // IsFiniteMeasure η}
  let obs : F → S → ℝ := fun η i => (η.1 i.1).toReal
  let m : MeasurableSpace F := MeasurableSpace.comap obs inferInstance
  have heval (i : S) : @Measurable F ℝ≥0∞ m _ (fun η => η.1 i.1) := by
    have hreal : @Measurable F ℝ m _ (fun η => obs η i) :=
      (measurable_pi_apply i).comp (comap_measurable obs)
    have h := ENNReal.measurable_ofReal.comp hreal
    convert h using 1
    funext η
    let : IsFiniteMeasure η.1 := η.2
    exact (ENNReal.ofReal_toReal (measure_ne_top η.1 i.1)).symm
  have hmeasure : @Measurable F (Measure ℂ) m _ Subtype.val := by
    let : MeasurableSpace F := m
    have (η : F) : IsFiniteMeasure η.1 := η.2
    exact Measurable.measure_of_isPiSystem hgen hpi
      (fun V hV => heval ⟨V, hV⟩) (heval ⟨univ, huniv⟩)
  have hevent : MeasurableSet[m] {η : F | coneMassEvent η.1 Q M r z} :=
    hmeasure (measurableSet_coneMassEvent Q M r z hQ)
  obtain ⟨C, hC, hpre⟩ := hevent
  refine ⟨C, hC, ?_⟩
  intro μ U
  let η : F := ⟨normalizedRestriction μ U, inferInstance⟩
  have h := Set.ext_iff.mp hpre η
  exact h.symm


/-- A shared decoder of normalized masses on a generating pi-system gives
both cone-event representations, without assuming an event representation. -/
theorem coneMassEvent_representation_of_mass_decoder
    {Ω Ξ κ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (P' : Measure Ξ) (X : Ω → κ → ℝ) (X' : Ξ → κ → ℝ)
    (k : κ → ℝ) (S : Set (Set ℂ)) (hgen : (inferInstance : MeasurableSpace ℂ) =
      MeasurableSpace.generateFrom S) (hpi : IsPiSystem S) (huniv : univ ∈ S)
    (D : (κ → ℝ) → S → ℝ) (hD : Measurable D)
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) {U Q : Set ℂ}
    (M r : ℝ) (z : ℂ) (hU : MeasurableSet U)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z))
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ U)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ U)
    (hμ : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞ ∧
      ∀ i : S, D (X ω) i = (normalizedRestriction (μ ω) U i.1).toReal)
    (hν : ∀ᵐ ω ∂P', ν ω U ≠ 0 ∧ ν ω U ≠ ∞ ∧
      ∀ i : S, D (X' ω) i = (normalizedRestriction (ν ω) U i.1).toReal) :
    ∃ B : Set (κ → ℝ), MeasurableSet B ∧
      (∀ᵐ ω ∂P, coneMassEvent (μ ω) Q M r z ↔ (fun φ => X ω φ + k φ) ∈ B) ∧
      ∀ᵐ ω ∂P', coneMassEvent (ν ω) Q M r z ↔ (fun φ => X' ω φ + k φ) ∈ B := by
  obtain ⟨C, hC, hencode⟩ := exists_coneMassEvent_countable_encoding S hgen hpi huniv Q M r z hQ
  let u : Ω → S → ℝ := fun ω i => (normalizedRestriction (μ ω) U i.1).toReal
  let v : Ξ → S → ℝ := fun ω i => (normalizedRestriction (ν ω) U i.1).toReal
  have hu : ∀ᵐ ω ∂P, D (X ω) = u ω := by
    filter_upwards [hμ] with ω hω
    funext i
    exact hω.2.2 i
  have hv : ∀ᵐ ω ∂P', D (X' ω) = v ω := by
    filter_upwards [hν] with ω hω
    funext i
    exact hω.2.2 i
  obtain ⟨B, hBm, hB, hB'⟩ :=
    fixedShift_event_representation_with_insertion P P' X X' k D hD u v hu hv C hC
  refine ⟨B, hBm, ?_, ?_⟩
  · filter_upwards [hμ, hB] with ω hω hBω
    exact (coneMassEvent_normalizedRestriction_iff (μ ω) M r z hU hcone hgreen
      hω.1 hω.2.1).symm.trans ((hencode (μ ω) U).trans hBω)
  · filter_upwards [hν, hB'] with ω hω hBω
    exact (coneMassEvent_normalizedRestriction_iff (ν ω) M r z hU hcone hgreen
      hω.1 hω.2.1).symm.trans ((hencode (ν ω) U).trans hBω)


/-- The actual fixed-shift LQG limit is a measurable random measure: its
Weyl density is continuous, and uniqueness identifies the vague limit. -/
theorem IsWholePlaneGFF.aemeasurable_fixedShift_lqgMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : Continuous g)
    (μ ν : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : IsLQGMeasure P γ
      (fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g) ν) :
    AEMeasurable ν P := by
  have hl : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  obtain ⟨m, hm, hml, heq⟩ :=
    Section6.exists_measurable_locallyFinite_rep (hGFF.aemeasurable_lqgMeasure hμ) hl
  let w : Unit → ℂ → ℝ≥0∞ := fun _ x => ENNReal.ofReal (Real.exp (γ * g x))
  have hw : Measurable (Function.uncurry w) := by
    exact ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.comp (continuous_const.mul (hg.comp continuous_snd))).measurable
  have hmap : Measurable (fun ω => (m ω).withDensity (w ())) := by
    have h := (Section6.measurable_withDensity_locallyFinite w hw).comp
      ((hm.subtype_mk (h := hml)).prodMk (measurable_const : Measurable (fun _ : Ω => ())))
    exact h
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  have hνeq : ∀ᵐ ω ∂P, ν ω = (m ω).withDensity (w ()) := by
    filter_upwards [hμ, hν, hc, heq] with ω hμω hνω hcω heω
    have hW := Section6.isLQGLimit_addCircleAverage hμω hcω g hg
    rw [heω] at hW
    exact hνω.unique hW
  apply hmap.aemeasurable.congr
  filter_upwards [hνeq] with ω hω
  exact hω.symm


/-- The actual LQG limits of a field and its fixed smooth shift have the
same cone-event decoder on a common continuity ball of positive finite mass. -/
theorem IsWholePlaneGFF.exists_fixedShift_coneMassEvent_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hε : 0 < ε) (hεR : ε < R)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 R))
    (μ ν : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : IsLQGMeasure P γ
      (fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g) ν)
    (hfμ : ∀ᵐ ω ∂P, μ ω (frontier (ball (0 : ℂ) ε)) = 0)
    (hfν : ∀ᵐ ω ∂P, ν ω (frontier (ball (0 : ℂ) ε)) = 0)
    (hpμ : ∀ᵐ ω ∂P, μ ω (ball (0 : ℂ) ε) ≠ 0)
    (hpν : ∀ᵐ ω ∂P, ν ω (ball (0 : ℂ) ε) ≠ 0)
    (Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z))
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ ball 0 ε)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ ball 0 ε)
    (k : Section6.LocalTest (ball 0 ε) → ℝ) :
    ∃ B : Set (Section6.LocalTest (ball 0 ε) → ℝ), MeasurableSet B ∧
      (∀ᵐ ω ∂P, coneMassEvent (μ ω) Q M r z ↔
        (fun φ => hC ω φ.1.1 + k φ) ∈ B) ∧
      ∀ᵐ ω ∂P, coneMassEvent (ν ω) Q M r z ↔
        (fun φ => hC ω φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ) ∈ B := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hlμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hlν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  obtain ⟨S, hc, hpi, hu, ho, hgen, V, hm, hmono, hunion, hbuffer, hf, hf'⟩ :=
    exists_common_buffered_continuity_system P μ ν (hGFF.aemeasurable_lqgMeasure hμ)
      (hGFF.aemeasurable_fixedShift_lqgMeasure hg μ ν hμ hν) hlμ hlν hε hfμ hfν
  let : Countable S := hc.to_subtype
  have hp : ∀ᵐ ω ∂P, μ ω (⋃ n, V n) ≠ 0 ∧ μ ω (⋃ n, V n) ≠ ∞ := by
    filter_upwards [hlμ, hpμ] with ω hl hp
    let : IsLocallyFiniteMeasure (μ ω) := hl
    rw [hunion]
    exact ⟨hp, measure_ball_ne_top⟩
  have hp' : ∀ᵐ ω ∂P, ν ω (⋃ n, V n) ≠ 0 ∧ ν ω (⋃ n, V n) ≠ ∞ := by
    filter_upwards [hlν, hpν] with ω hl hp
    let : IsLocallyFiniteMeasure (ν ω) := hl
    rw [hunion]
    exact ⟨hp, measure_ball_ne_top⟩
  obtain ⟨D, hD, hDμ, hDν⟩ := hGFF.exists_fixedShift_normalizedMass_decoder
    hε hεR hg hgs μ ν hμ hν V hm hmono hbuffer hunion (fun i : S => i.1)
    (fun i => (ho i.1 i.2).measurableSet)
    (fun i => hf.mono fun _ h => h i.1 i.2)
    (fun i => hf'.mono fun _ h => h i.1 i.2) hp hp'
  apply coneMassEvent_representation_of_mass_decoder P P
    (Section6.localPairingProc (ball 0 ε) hC)
    (fun ω φ => hC ω φ.1.1 + ∫ x, φ.1.1 x * g x) k S hgen hpi hu D hD
    μ ν M r z measurableSet_ball hQ hcone hgreen
  · filter_upwards [hp, hDμ] with ω hp hDω
    rw [hunion] at hp
    exact ⟨hp.1, hp.2, hDω⟩
  · filter_upwards [hp', hDν] with ω hp hDω
    rw [hunion] at hp
    exact ⟨hp.1, hp.2, hDω⟩


/-- A common continuity ball can be chosen around the cone and Green
annuli, and the actual fixed-shift LQG limits then have one local event
decoder. Full support is used only to ensure positive reference mass. -/
theorem IsWholePlaneGFF.exists_enclosing_fixedShift_coneMassEvent_representation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ L R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hL : 0 < L) (hLR : L < R)
    {g : ℂ → ℝ} (hg : Continuous g)
    (hgs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g (ball 0 R))
    (μ ν : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hν : IsLQGMeasure P γ
      (fun ω => addCircleAverage (fieldCircleAverage α₀ (hcirc ω)) g) ν)
    (hfullμ : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (Q : Set ℂ) (M r : ℝ) (z : ℂ)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z))
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ ball 0 L)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ ball 0 L) :
    ∃ ε ∈ Ioo L R, ∀ k : Section6.LocalTest (ball 0 ε) → ℝ,
      ∃ B : Set (Section6.LocalTest (ball 0 ε) → ℝ), MeasurableSet B ∧
        (∀ᵐ ω ∂P, coneMassEvent (μ ω) Q M r z ↔
          (fun φ => hC ω φ.1.1 + k φ) ∈ B) ∧
        ∀ᵐ ω ∂P, coneMassEvent (ν ω) Q M r z ↔
          (fun φ => hC ω φ.1.1 + (∫ x, φ.1.1 x * g x) + k φ) ∈ B := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hlμ : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) :=
    hμ.mono fun _ h => h.isLocallyFiniteMeasure
  have hlν : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  obtain ⟨ε, hε, hfμ, hfν⟩ := exists_common_continuity_ball P μ ν
    (hGFF.aemeasurable_lqgMeasure hμ)
    (hGFF.aemeasurable_fixedShift_lqgMeasure hg μ ν hμ hν) hlμ hlν hLR
  have hεpos : 0 < ε := lt_trans hL hε.1
  have hpμ : ∀ᵐ ω ∂P, μ ω (ball (0 : ℂ) ε) ≠ 0 := by
    filter_upwards [hfullμ] with ω hω
    exact (hω _ isOpen_ball ⟨0, mem_ball_self hεpos⟩).ne'
  have hc : ∀ᵐ ω ∂P, ∀ n, Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr fun n => hGFF.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  have hpν : ∀ᵐ ω ∂P, ν ω (ball (0 : ℂ) ε) ≠ 0 := by
    filter_upwards [hμ, hν, hc, hpμ] with ω hμω hνω hcω hpω
    have hW := Section6.isLQGLimit_addCircleAverage hμω hcω g hg
    have heq := hνω.unique hW
    have hac : μ ω ≪ ν ω := by
      rw [heq]
      apply withDensity_absolutelyContinuous'
      · exact (ENNReal.measurable_ofReal.comp
          (Real.continuous_exp.comp (continuous_const.mul hg)).measurable).aemeasurable
      · exact ae_of_all _ fun x => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
    exact fun hz => hpω (hac hz)
  refine ⟨ε, hε, fun k => ?_⟩
  exact hGFF.exists_fixedShift_coneMassEvent_representation hεpos hε.2 hg hgs
    μ ν hμ hν hfμ hfν hpμ hpν Q M r z hQ
    (hcone.trans (ball_subset_ball hε.1.le))
    (hgreen.trans (ball_subset_ball hε.1.le)) k


/-- A common measurable decoder of normalized local measures produces both
cone-event representations, with an arbitrary deterministic insertion. -/
theorem coneMassEvent_representation_of_measure_decoder
    {Ω Ξ κ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (P : Measure Ω) (P' : Measure Ξ) (X : Ω → κ → ℝ) (X' : Ξ → κ → ℝ)
    (k : κ → ℝ) (D : (κ → ℝ) → Measure ℂ) (hD : Measurable D)
    (μ : Ω → Measure ℂ) (ν : Ξ → Measure ℂ) {U Q : Set ℂ}
    (M r : ℝ) (z : ℂ) (hU : MeasurableSet U)
    (hQ : MeasurableSet (annulus z r (2 * r) ∩ coneAt Q z))
    (hcone : annulus z r (2 * r) ∩ coneAt Q z ⊆ U)
    (hgreen : annulus z (3 * r) (6 * r) ⊆ U)
    (hμ : ∀ᵐ ω ∂P, μ ω U ≠ 0 ∧ μ ω U ≠ ∞ ∧
      D (X ω) = normalizedRestriction (μ ω) U)
    (hν : ∀ᵐ ω ∂P', ν ω U ≠ 0 ∧ ν ω U ≠ ∞ ∧
      D (X' ω) = normalizedRestriction (ν ω) U) :
    ∃ B : Set (κ → ℝ), MeasurableSet B ∧
      (∀ᵐ ω ∂P, coneMassEvent (μ ω) Q M r z ↔ (fun φ => X ω φ + k φ) ∈ B) ∧
      ∀ᵐ ω ∂P', coneMassEvent (ν ω) Q M r z ↔ (fun φ => X' ω φ + k φ) ∈ B := by
  let T : (κ → ℝ) → (κ → ℝ) := fun x φ => x φ - k φ
  have hT : Measurable T := measurable_pi_iff.mpr fun φ =>
    (measurable_pi_apply φ).sub_const _
  refine ⟨(D ∘ T) ⁻¹' {η | coneMassEvent η Q M r z},
    (hD.comp hT) (measurableSet_coneMassEvent Q M r z hQ), ?_, ?_⟩
  · filter_upwards [hμ] with ω hω
    have heq : T (fun φ => X ω φ + k φ) = X ω := by
      funext φ
      simp [T]
    change coneMassEvent (μ ω) Q M r z ↔ coneMassEvent (D (T _)) Q M r z
    rw [heq, hω.2.2]
    exact (coneMassEvent_normalizedRestriction_iff (μ ω) M r z hU hcone hgreen
      hω.1 hω.2.1).symm
  · filter_upwards [hν] with ω hω
    have heq : T (fun φ => X' ω φ + k φ) = X' ω := by
      funext φ
      simp [T]
    change coneMassEvent (ν ω) Q M r z ↔ coneMassEvent (D (T _)) Q M r z
    rw [heq, hω.2.2]
    exact (coneMassEvent_normalizedRestriction_iff (ν ω) M r z hU hcone hgreen
      hω.1 hω.2.1).symm


end HarmonicBalls
