import HarmonicBalls.Proofs.Sec8.PhaseTorus
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-! # Lebesgue-almost-every lattice phase

The quotient map from the plane to the phase torus sends planar Lebesgue
measure to a measure absolutely continuous with respect to torus Haar measure.
-/

open MeasureTheory MeasureTheory.Measure Set

namespace HarmonicBalls

/-- The quotient map from the real line to the unit circle sends null sets
back to null sets, using the countable cover by unit intervals. -/
theorem quasiMeasurePreserving_phaseCircle_quotient :
    QuasiMeasurePreserving (fun x : ℝ => (x : PhaseCircle))
      (volume : Measure ℝ) (volume : Measure PhaseCircle) := by
  refine ⟨AddCircle.measurable_mk', ?_⟩
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  rw [Measure.map_apply AddCircle.measurable_mk' hs]
  rw [measure_eq_zero_iff_ae_notMem] at hzero ⊢
  have hi : ∀ n : ℤ, ∀ᵐ x ∂((volume : Measure ℝ).restrict (Ioc (n : ℝ) (n + 1))),
      ((x : ℝ) : PhaseCircle) ∉ s := by
    intro n
    exact (AddCircle.measurePreserving_mk (1 : ℝ) (n : ℝ)).quasiMeasurePreserving.ae hzero
  have hu := (ae_restrict_iUnion_iff (fun n : ℤ => Ioc (n : ℝ) (n + 1))
    (fun x : ℝ => ((x : ℝ) : PhaseCircle) ∉ s)).2 hi
  change ∀ᵐ x ∂(volume : Measure ℝ), ((x : ℝ) : PhaseCircle) ∉ s
  simpa only [iUnion_Ioc_intCast, Measure.restrict_univ] using hu

/-- A planar Lebesgue-typical point has a torus phase outside every Haar-null
set. The period `1 / 100` is accounted for by the dilation by `100`. -/
theorem quasiMeasurePreserving_phaseTorusOfComplex :
    QuasiMeasurePreserving phaseTorusOfComplex (volume : Measure ℂ)
      ((volume : Measure PhaseCircle).prod volume) := by
  have hscale : QuasiMeasurePreserving (fun z : ℂ => (100 : ℝ) • z)
      (volume : Measure ℂ) volume :=
    Measure.quasiMeasurePreserving_smul volume (by norm_num)
  have hreal := Complex.volume_preserving_equiv_real_prod.quasiMeasurePreserving
  have hquot := MeasureTheory.QuasiMeasurePreserving.prodMap quasiMeasurePreserving_phaseCircle_quotient
    quasiMeasurePreserving_phaseCircle_quotient
  have h := hquot.comp (hreal.comp hscale)
  convert h using 1
  funext z
  apply Prod.ext <;> simp [phaseTorusOfComplex, Complex.measurableEquivRealProd]

/-- A Haar-almost-every phase property holds for the torus phase of
Lebesgue-almost-every centre. -/
theorem ae_phaseTorusOfComplex_of_ae {A : PhaseTorus → Prop}
    (hA : ∀ᵐ p ∂((volume : Measure PhaseCircle).prod volume), A p) :
    ∀ᵐ z ∂(volume : Measure ℂ), A (phaseTorusOfComplex z) :=
  quasiMeasurePreserving_phaseTorusOfComplex.ae hA

/-- A phase/field property holding almost surely for independent Haar phase
and field also holds for almost every centre under any measure dominated by
planar Lebesgue measure, and then for almost every field. This statement does
not assume independence of a random-measure root. -/
theorem ae_ae_negative_centerPhase_of_ae_prod
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) {A : PhaseTorus → Ω → Prop}
    (hA : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P), A p.1 p.2) :
    ∀ᵐ z ∂ρ, ∀ᵐ ω ∂P, A (phaseTorusOfComplex (-z)) ω := by
  have hfib : ∀ᵐ p ∂((volume : Measure PhaseCircle).prod volume), ∀ᵐ ω ∂P, A p ω :=
    Measure.ae_ae_of_ae_prod hA
  have hneg : QuasiMeasurePreserving (fun z : ℂ => -z) (volume : Measure ℂ) volume := by
    simpa only [neg_one_smul] using
      (Measure.quasiMeasurePreserving_smul (volume : Measure ℂ) (r := (-1 : ℝ)) (by norm_num))
  exact hρ.ae_le ((quasiMeasurePreserving_phaseTorusOfComplex.comp hneg).ae hfib)

/-- The preceding phase transfer remains valid for centre-dependent field
laws dominated by the reference field law. -/
theorem ae_ae_negative_centerPhase_of_ae_prod_of_dominated
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) (R : ℂ → Measure Ω)
    (hdom : ∀ᵐ z ∂ρ, R z ≪ P) {A : PhaseTorus → Ω → Prop}
    (hA : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P), A p.1 p.2) :
    ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(R z), A (phaseTorusOfComplex (-z)) ω := by
  filter_upwards [ae_ae_negative_centerPhase_of_ae_prod P ρ hρ hA, hdom] with z hz hR
  exact hR.ae_le hz

/-- At every dyadic scale, recentering an absolute-lattice very-good annulus
uses the torus class of the negative centre. -/
theorem isVeryGoodAnnulus_iff_centered_torusPhase (μ : Measure ℂ) (β : ℝ)
    (z : ℂ) (n N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus μ β (dyadicScale n) z N a b C₁m C₁p C₂m C₂p C₃ ↔
      PhaseVeryGoodAnnulus (μ.map (fun w : ℂ => w - z)) β (dyadicScale n) 0 N
        a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-z))) := by
  rw [isVeryGoodAnnulus_iff_centered_shifted_phase]
  change PhaseVeryGoodAnnulus (μ.map (fun w : ℂ => w - z)) β (dyadicScale n) 0 N
    a b C₁m C₁p C₂m C₂p C₃ (-z) ↔ _
  exact (phaseVeryGoodAnnulus_torusPhase_ofComplex _ β n N
    a b C₁m C₁p C₂m C₂p C₃ (-z)).symm

/-- The annulus-ball comparison is unchanged when the measure is recentered. -/
theorem annulusBallComparison_map_sub (μ : Measure ℂ) (z : ℂ) (n : ℕ) (m : ℝ) :
    AnnulusBallComparison (μ.map (fun w : ℂ => w - z)) n 0 m ↔
      AnnulusBallComparison μ n z m := by
  have hb : (μ.map (fun w : ℂ => w - z)) (Metric.ball 0 (dyadicScale n)) =
      μ (Metric.ball z (dyadicScale n)) := by
    rw [Measure.map_apply (by fun_prop) Metric.isOpen_ball.measurableSet]
    congr 1
    ext w
    simp [Metric.mem_ball, dist_eq_norm]
  simp only [AnnulusBallComparison, hb, Section6.map_sub_annulus]

/-- The printed block count at a centre equals the phase-shifted block count
of the recentered measure. -/
theorem veryGoodComparableScaleCount_eq_centered_torus (μ : Measure ℂ) (β : ℝ)
    (z : ℂ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (N : ℕ) :
    veryGoodComparableScaleCount μ β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N =
      ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (μ.map (fun w : ℂ => w - z)) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase (phaseTorusOfComplex (-z))) ∧
        AnnulusBallComparison (μ.map (fun w : ℂ => w - z)) n 0 m}.ncard) := by
  unfold veryGoodComparableScaleCount
  congr 1
  ext n
  simp only [mem_ofPred_eq, isVeryGoodAnnulus_iff_centered_torusPhase,
    annulusBallComparison_map_sub]

/-- A phase/field block-frequency estimate transfers to translated measures
under Lebesgue-dominated centre laws and dominated comparison field laws,
provided the comparison measure is the recentered original measure. -/
theorem ae_ae_veryGoodComparableScaleFrequency_of_phase_torus
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (ρ : Measure ℂ) (hρ : ρ ≪ volume) (R : ℂ → Measure Ω)
    (hdom : ∀ᵐ z ∂ρ, R z ≪ P)
    (μ : Ω → Measure ℂ) (M : ℂ → Ω → Measure ℂ)
    (hcenter : ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(R z),
      (M z ω).map (fun w : ℂ => w - z) = μ ω)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ N : ℕ in Filter.atTop,
        (1 - ζ) * (N : ℝ) ≤
          (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
            PhaseVeryGoodAnnulus (μ p.2) β (dyadicScale n) 0 N₀
              a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
            AnnulusBallComparison (μ p.2) n 0 m}.ncard : ℕ) : ℝ)) :
    ∀ᵐ z ∂ρ, ∀ᵐ ω ∂(R z), ∀ᶠ N : ℕ in Filter.atTop,
      (1 - ζ) * (N : ℝ) ≤ (veryGoodComparableScaleCount (M z ω) β z N₀
        a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  let A : PhaseTorus → Ω → Prop := fun t ω =>
    ∀ᶠ N : ℕ in Filter.atTop, (1 - ζ) * (N : ℝ) ≤
      (({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
        PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
        AnnulusBallComparison (μ ω) n 0 m}.ncard : ℕ) : ℝ)
  have htrans := ae_ae_negative_centerPhase_of_ae_prod_of_dominated P ρ hρ R hdom
    (A := A) hphase
  filter_upwards [htrans, hcenter] with z hz hc
  filter_upwards [hz, hc] with ω hω hcω
  filter_upwards [hω] with N hN
  rw [veryGoodComparableScaleCount_eq_centered_torus, hcω]
  exact hN

end HarmonicBalls
