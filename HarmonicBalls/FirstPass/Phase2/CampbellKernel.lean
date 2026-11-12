import HarmonicBalls.FirstPass.Phase2.DMSJointPosOfFinite

/-!
# Kernels of the marked Campbell identity (Duplantier-Miller-Sheffield Lemma A.10)

For a whole-plane GFF `h` and its `γ`-LQG measure `μ` (insertion `α = 0`), the two sides of the marked identity
`DMSLemmaA10WholePlaneMarkedSub` (FirstPass/Frozen/S11i.lean:59) are integrals against two measures on the observation
space `MarkObs = pairing × mark`, with the pairing σ-algebra of test functions on `ℂ` on the first factor:
* the rooted measure `markedLeftMeas = P.bind (ω ↦ (ρ ω).map (z ↦ (h(ω), z)))`, where `ρ` is a measurable version of
  the restriction of `μ` to the unit disc `B₁` with finite fibres (`exists_measurable_finite_restrict`);
* the DMS-shifted measure `markedRightMeas = (Leb|B₁).bind (z ↦ P.map (ω ↦ (h(ω) + γ G(z, ·) - c_z(ω), z)))`.

The measurable version comes from the profile decoder `lqgMeasureOfProfileMeasurable_derived` and the local finiteness of
the LQG measure (no mass identity is used). The main statement of the file, `lintegral_marked_eq_of_measures_eq`,
reduces the marked identity for every measurable test `Ψ` to the equality of the two measures.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal NNReal

namespace HarmonicBalls

universe u

namespace CampbellKernel

/-- The observation space of the marked identity: the pairing functional and the mark. -/
abbrev MarkObs : Type := ((ℂ → ℝ) → ℝ) × ℂ

/-- The σ-algebra of `MarkObs`: the pairing σ-algebra of the test functions on `ℂ` on the first factor and the Borel
σ-algebra of `ℂ` on the mark. It is the σ-algebra of the tests `Ψ` of `DMSLemmaA10WholePlaneMarkedSub`. -/
noncomputable abbrev markObsSigma : MeasurableSpace MarkObs :=
  (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance

attribute [local instance] markObsSigma

/-- The field observed at the mark: `(ω, z) ↦ (h(ω), z)`. -/
def obsM {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (q : Ω × ℂ) : MarkObs := (hC q.1, q.2)

/-- The DMS-shifted field observed at the shift: `(z, ω) ↦ (dmsShiftedPairing γ z h(ω) h₁(0)(ω), z)`. -/
noncomputable def obsMs {Ω : Type*} (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (q : ℂ × Ω) :
    MarkObs :=
  (dmsShiftedPairing γ q.1 (hC q.2) (hcirc q.2 1 0), q.1)

/-- **The field observation is measurable.** -/
theorem measurable_obsM {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) : Measurable (obsM hC) :=
  Measurable.prodMk ((FirstPassS11atProducers.measurable_into_pairing hC fun φ hφ =>
    hW.measurable_pairing φ hφ).comp measurable_fst) measurable_snd

/-- **The DMS-shifted observation is measurable** (`FirstPassS11atProducers.measurable_dmsShiftedPairing`). -/
theorem measurable_obsMs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (γ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) : Measurable (obsMs γ hC hcirc) :=
  Measurable.prodMk (FirstPassS11atProducers.measurable_dmsShiftedPairing P γ hC hcirc hW) measurable_fst

/-- **A measurable version of the LQG measure on the unit disc with finite fibres.** For a whole-plane GFF and its
`α = 0` LQG measure `μ`, there is a measurable family `ρ` of finite measures with `μ_ω|_{B₁} = ρ ω` almost surely. The
version is `finRestr (Dec ∘ F)` for the continuous circle profile `F` and the profile decoder `Dec`
(`lqgMeasureOfProfileMeasurable_derived`); the masses `μ_ω(B₁)` are almost surely finite because `μ_ω` is a Radon
measure (`IsLQGLimit.isLocallyFiniteMeasure`). -/
theorem exists_measurable_finite_restrict {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hW : IsWholePlaneGFF P hC hcirc) (hL : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∃ ρ : Ω → Measure ℂ, Measurable ρ ∧ (∀ ω, IsFiniteMeasure (ρ ω)) ∧
      ∀ᵐ ω ∂P, (μ ω).restrict (ball (0 : ℂ) 1) = ρ ω := by
  obtain ⟨F, hFm, -, hF⟩ := hW.exists_measurable_continuous_circle_version
  obtain ⟨Dec, hDecm, hμDec, -⟩ :=
    lqgMeasureOfProfileMeasurable_derived Ω P γ 0 hC hcirc μ F hW hL hFm hF
  have hμ'm : Measurable (fun ω => Dec (F ω)) := hDecm.comp hFm
  have hL' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (μ ω) := hL
  have hfin : ∀ᵐ ω ∂P, Dec (F ω) (ball (0 : ℂ) 1) < ∞ := by
    filter_upwards [hμDec, hL'] with ω h1 h2
    rw [← h1]
    have := h2.isLocallyFiniteMeasure
    exact measure_ball_lt_top
  refine ⟨DMSFiniteTiltPosDerived.finRestr (fun ω => Dec (F ω)),
    DMSFiniteTiltPosDerived.measurable_finRestr hμ'm,
    DMSFiniteTiltPosDerived.isFiniteMeasure_finRestr _, ?_⟩
  filter_upwards [hμDec, hfin] with ω h1 h2
  rw [h1]
  simp [DMSFiniteTiltPosDerived.finRestr, h2]

/-- The rooted kernel `ω ↦ (ρ ω).map (z ↦ (h(ω), z))`. -/
noncomputable def markedLeftKernel {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (ρ : Ω → Measure ℂ) (ω : Ω) :
    Measure MarkObs :=
  (ρ ω).map fun z => obsM hC (ω, z)

/-- The shifted kernel `z ↦ P.map (ω ↦ (dmsShiftedPairing γ z h(ω) h₁(0)(ω), z))`. -/
noncomputable def markedRightKernel {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) : Measure MarkObs :=
  P.map fun ω => obsMs γ hC hcirc (z, ω)

/-- The rooted measure `P.bind (ω ↦ (ρ ω).map (z ↦ (h(ω), z)))` (left side of the marked identity). -/
noncomputable def markedLeftMeas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
    (ρ : Ω → Measure ℂ) : Measure MarkObs :=
  P.bind (markedLeftKernel hC ρ)

/-- The DMS-shifted measure `(Leb|B₁).bind (z ↦ P.map (ω ↦ (dmsShiftedPairing γ z h(ω) h₁(0)(ω), z)))` (right
side of the marked identity). -/
noncomputable def markedRightMeas {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) : Measure MarkObs :=
  (volume.restrict (ball (0 : ℂ) 1)).bind (markedRightKernel P γ hC hcirc)

/-- **The rooted kernel is measurable** (`Measure.measurable_of_measurable_coe`; the mass of a measurable set is a
lintegral against a measurable family of finite measures). -/
theorem measurable_markedLeftKernel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) {ρ : Ω → Measure ℂ} (hρ : Measurable ρ)
    (hfin : ∀ ω, IsFiniteMeasure (ρ ω)) : Measurable (markedLeftKernel hC ρ) := by
  have hG := measurable_obsM hW
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hA : MeasurableSet (obsM hC ⁻¹' S) := hG hS
  have hsl : ∀ ω, markedLeftKernel hC ρ ω S
      = ∫⁻ z, (obsM hC ⁻¹' S).indicator (1 : Ω × ℂ → ℝ≥0∞) (ω, z) ∂(ρ ω) := by
    intro ω
    have hm : Measurable fun z => obsM hC (ω, z) := hG.comp measurable_prodMk_left
    have hs : MeasurableSet ((fun z => obsM hC (ω, z)) ⁻¹' S) := hm hS
    rw [markedLeftKernel, Measure.map_apply hm hS, ← lintegral_indicator_one hs]
    refine lintegral_congr fun z => ?_
    rfl
  have hfun : (fun ω => markedLeftKernel hC ρ ω S)
      = fun ω => ∫⁻ z, (obsM hC ⁻¹' S).indicator (1 : Ω × ℂ → ℝ≥0∞) (ω, z) ∂(ρ ω) :=
    funext hsl
  rw [hfun]
  exact DMSFiniteTiltPosDerived.measurable_lintegral_finite_family ρ hρ hfin
    (measurable_one.indicator hA)

/-- **The shifted kernel is measurable** (`measurable_measure_prodMk_left`). -/
theorem measurable_markedRightKernel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) :
    Measurable (markedRightKernel P γ hC hcirc) := by
  have hGs := measurable_obsMs γ hW
  refine Measure.measurable_of_measurable_coe _ fun S hS => ?_
  have hfun : (fun z => markedRightKernel P γ hC hcirc z S)
      = fun z => P (Prod.mk z ⁻¹' (obsMs γ hC hcirc ⁻¹' S)) := by
    funext z
    have hm : Measurable fun ω => obsMs γ hC hcirc (z, ω) := hGs.comp measurable_prodMk_left
    rw [markedRightKernel, Measure.map_apply hm hS]
    rfl
  rw [hfun]
  exact measurable_measure_prodMk_left (hGs hS)

/-- **The DMS-shifted measure is finite**, of total mass `Leb(B₁) = π`. -/
theorem markedRightMeas_univ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hW : IsWholePlaneGFF P hC hcirc) :
    markedRightMeas P γ hC hcirc Set.univ = volume (ball (0 : ℂ) 1) := by
  rw [markedRightMeas, Measure.bind_apply MeasurableSet.univ
    (measurable_markedRightKernel (P := P) (γ := γ) hW).aemeasurable]
  have hk : ∀ z, markedRightKernel P γ hC hcirc z Set.univ = 1 := fun z => by
    have hm : Measurable fun ω => obsMs γ hC hcirc (z, ω) := (measurable_obsMs γ hW).comp measurable_prodMk_left
    rw [markedRightKernel, Measure.map_apply hm MeasurableSet.univ]
    simp
  simp [hk]

theorem isFiniteMeasure_markedRightMeas {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) : IsFiniteMeasure (markedRightMeas P γ hC hcirc) :=
  ⟨by rw [markedRightMeas_univ hW]; exact measure_ball_lt_top⟩

/-- **Reduction to the measure identity.** If the rooted measure of a measurable finite version `ρ` of `μ|_{B₁}`
equals the DMS-shifted measure, the marked identity of `DMSLemmaA10WholePlaneMarkedSub` holds for every measurable
test `Ψ` (`Measure.lintegral_bind`, `lintegral_map`). -/
theorem lintegral_marked_eq_of_measures_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ρ : Ω → Measure ℂ}
    (hW : IsWholePlaneGFF P hC hcirc) (hρ : Measurable ρ) (hfin : ∀ ω, IsFiniteMeasure (ρ ω))
    (hρμ : ∀ᵐ ω ∂P, (μ ω).restrict (ball (0 : ℂ) 1) = ρ ω)
    (hLR : markedLeftMeas P hC ρ = markedRightMeas P γ hC hcirc)
    (Ψ : MarkObs → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω) ∂P
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume := by
  have hG := measurable_obsM hW
  have hGs := measurable_obsMs γ hW
  have hk := measurable_markedLeftKernel hW hρ hfin
  have hk2 := measurable_markedRightKernel (P := P) (γ := γ) hW
  have hA : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, Ψ (hC ω, z) ∂(μ ω) ∂P
      = ∫⁻ ω, ∫⁻ x, Ψ x ∂(markedLeftKernel hC ρ ω) ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hρμ] with ω hω
    have hm : Measurable fun z => obsM hC (ω, z) := hG.comp measurable_prodMk_left
    rw [markedLeftKernel, lintegral_map hΨ hm, ← hω]
    rfl
  have hL : ∫⁻ x, Ψ x ∂(markedLeftMeas P hC ρ) = ∫⁻ ω, ∫⁻ x, Ψ x ∂(markedLeftKernel hC ρ ω) ∂P :=
    Measure.lintegral_bind hk.aemeasurable hΨ.aemeasurable
  have hR : ∫⁻ x, Ψ x ∂(markedRightMeas P γ hC hcirc)
      = ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, Ψ (dmsShiftedPairing γ z (hC ω) (hcirc ω 1 0), z) ∂P ∂volume := by
    rw [markedRightMeas, Measure.lintegral_bind hk2.aemeasurable hΨ.aemeasurable]
    refine lintegral_congr fun z => ?_
    have hm : Measurable fun ω => obsMs γ hC hcirc (z, ω) := hGs.comp measurable_prodMk_left
    rw [markedRightKernel, lintegral_map hΨ hm]
    rfl
  rw [hA, ← hL, hLR, hR]

end CampbellKernel

end HarmonicBalls
