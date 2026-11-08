import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmPsiExtension
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmMarkedMeasures
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmCylinderPiSystem

/-! # Route (A), Step M: the left and right marked measures agree (P3.6)

`markedLeft P hC κ = P.bind (ω ↦ (κ ω).map (z ↦ (hC ω, z)))` and `markedRight P γ hC` are measures on the pairing
space times `ℂ`. On a rectangle `A × B` (`A` a cylinder over finitely many test functions, `B` Borel) both values are
the Palm integrals of `1_A` against `κ_ω(B)` resp. the shifted expectation over `B ∩ B₁` (`lintegral_markedLeft`,
`lintegral_markedRight`). They agree by the ψ-extension `lintegral_palm_psi` with `ψ = 1_U`. Their total masses agree
(both equal the volume of `B₁`, by the Palm identity with `ψ ≡ 1`). Finite measures are then equal by
`ext_marked_of_cylinder` (r10 `l:r9-marked`, the marked assembly). -/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace HarmonicBalls

/-- The value of the left marked measure on a rectangle `A × B`. -/
theorem markedLeft_prod_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {hC : Ω → (ℂ → ℝ) → ℝ}
    {κ : Ω → Measure ℂ}
    (hκs : ∀ S : Set (PairFun × ℂ), MeasurableSet[MeasurableSpace.prod inferInstance inferInstance] S →
      Measurable fun ω => κ ω {z | (toPairFun (hC ω), z) ∈ S})
    {A : Set PairFun} (hA : MeasurableSet A) {B : Set ℂ} (hB : MeasurableSet B) :
    markedLeft P hC κ (A ×ˢ B) = ∫⁻ ω, A.indicator (1 : PairFun → ℝ≥0∞) (toPairFun (hC ω)) * κ ω B ∂P := by
  have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
  have hΨ : Measurable ((A ×ˢ B).indicator (1 : PairFun × ℂ → ℝ≥0∞)) :=
    measurable_const.indicator hAB
  rw [← lintegral_indicator_one hAB, lintegral_markedLeft P hκs hΨ]
  refine lintegral_congr fun ω => ?_
  have hpt : ∀ z : ℂ, (A ×ˢ B).indicator (1 : PairFun × ℂ → ℝ≥0∞) (toPairFun (hC ω), z) =
      A.indicator (1 : PairFun → ℝ≥0∞) (toPairFun (hC ω)) * B.indicator (1 : ℂ → ℝ≥0∞) z := by
    intro z
    by_cases hT : toPairFun (hC ω) ∈ A <;> by_cases hz : z ∈ B <;>
      simp [hT, hz, Set.mem_prod]
  have hr : A.indicator (1 : PairFun → ℝ≥0∞) (toPairFun (hC ω)) ≠ ⊤ := by
    by_cases hT : toPairFun (hC ω) ∈ A <;> simp [hT]
  simp only [hpt]
  rw [lintegral_const_mul' _ _ hr, lintegral_indicator_one hB]

/-- The value of the right marked measure on a rectangle `A × B`: the shifted expectation of `1_A`, integrated over
`B ∩ B₁`. -/
theorem markedRight_prod_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] (γ : ℝ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {A : Set PairFun} (hA : MeasurableSet A) {B : Set ℂ} (hB : MeasurableSet B) :
    markedRight P γ hC (A ×ˢ B) =
      ∫⁻ z in B ∩ ball (0 : ℂ) 1, ∫⁻ ω, A.indicator (1 : PairFun → ℝ≥0∞)
        (toPairFun (shiftedPairing γ z (hC ω))) ∂P ∂(volume : Measure ℂ) := by
  have hAB : MeasurableSet (A ×ˢ B) := hA.prod hB
  have hΨ : Measurable ((A ×ˢ B).indicator (1 : PairFun × ℂ → ℝ≥0∞)) :=
    measurable_const.indicator hAB
  have hpt : ∀ z : ℂ, ∫⁻ ω, (A ×ˢ B).indicator (1 : PairFun × ℂ → ℝ≥0∞)
        (toPairFun (shiftedPairing γ z (hC ω)), z) ∂P =
      B.indicator (fun z : ℂ => ∫⁻ ω, A.indicator (1 : PairFun → ℝ≥0∞)
        (toPairFun (shiftedPairing γ z (hC ω))) ∂P) z := by
    intro z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz]
      refine lintegral_congr fun ω => ?_
      by_cases hT : toPairFun (shiftedPairing γ z (hC ω)) ∈ A <;> simp [hT, hz, Set.mem_prod]
    · rw [Set.indicator_of_notMem hz]
      have h0 : ∀ ω, (A ×ˢ B).indicator (1 : PairFun × ℂ → ℝ≥0∞)
          (toPairFun (shiftedPairing γ z (hC ω)), z) = 0 := fun ω => by
        simp [hz, Set.mem_prod]
      simp [h0]
  rw [← lintegral_indicator_one hAB, lintegral_markedRight γ hG hΨ]
  simp only [hpt]
  rw [lintegral_indicator hB, Measure.restrict_restrict hB]

/-- **Marked left equals marked right**: for a random kernel `κ` equal to `μ|_{B₁}` almost surely, with
measurable sections, the left marked measure (`markedLeft`) equals the right one (`markedRight`). The unnormalized
DMS hypothesis `hU` stays explicit. -/
theorem markedLeft_eq_markedRight {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hU : DMSLemmaA10WholePlaneUnnormalized P γ hC hcirc μ)
    {κ : Ω → Measure ℂ} (hκm : Measurable κ) (hκa : ∀ᵐ ω ∂P, κ ω = (μ ω).restrict (ball (0 : ℂ) 1))
    (hκs : ∀ S : Set (PairFun × ℂ), MeasurableSet[MeasurableSpace.prod inferInstance inferInstance] S →
      Measurable fun ω => κ ω {z | (toPairFun (hC ω), z) ∈ S}) :
    markedLeft P hC κ = markedRight P γ hC := by
  -- `κ ω B = κ ω (B ∩ B₁)` for almost every `ω`
  have hsupp : ∀ B : Set ℂ, MeasurableSet B → ∀ᵐ ω ∂P, κ ω B = κ ω (B ∩ ball (0 : ℂ) 1) := by
    intro B hB
    filter_upwards [hκa] with ω hω
    rw [hω, Measure.restrict_apply hB, Measure.restrict_apply (hB.inter measurableSet_ball),
      Set.inter_assoc, Set.inter_self]
  -- the total mass of `κ_ω(B₁)`: the Palm identity with `ψ ≡ 1` and the empty family of test functions
  have hmass : ∫⁻ ω, κ ω (Set.univ ∩ ball (0 : ℂ) 1) ∂P = volume (Set.univ ∩ ball (0 : ℂ) 1) := by
    have h1 := lintegral_palm_open hG γ hμ hU hκm hκa isOpen_univ (φ := fun j : Fin 0 => j.elim0)
      (fun j => j.elim0) (continuous_const : Continuous fun _ : Fin 0 → ℝ => (1 : ℝ))
      (fun _ => zero_le_one) (C := 1) (fun _ => by simp)
    simp only [ENNReal.ofReal_one, one_mul, lintegral_const, measure_univ, mul_one,
      Measure.restrict_apply_univ] at h1
    exact h1
  -- the two total masses are both the volume of `B₁`
  have hLuniv : markedLeft P hC κ Set.univ = volume (Set.univ ∩ ball (0 : ℂ) 1) := by
    have h := markedLeft_prod_eq P hκs MeasurableSet.univ MeasurableSet.univ
    rw [Set.univ_prod_univ] at h
    rw [h]
    simp only [Set.indicator_univ, Pi.one_apply, one_mul]
    rw [lintegral_congr_ae (hsupp Set.univ MeasurableSet.univ)]
    exact hmass
  have hRuniv : markedRight P γ hC Set.univ = volume (Set.univ ∩ ball (0 : ℂ) 1) := by
    have h := markedRight_prod_eq γ hG MeasurableSet.univ MeasurableSet.univ
    rw [Set.univ_prod_univ] at h
    rw [h]
    simp only [Set.indicator_univ, Pi.one_apply, lintegral_one, measure_univ,
      Measure.restrict_apply_univ]
  have hfin : IsFiniteMeasure (markedLeft P hC κ) := by
    refine ⟨?_⟩
    rw [hLuniv, Set.univ_inter]
    exact measure_ball_lt_top
  -- on cylinders × Borel sets
  have hcyl : ∀ A ∈ cylinderSets, ∀ B : Set ℂ, MeasurableSet B →
      markedLeft P hC κ (A ×ˢ B) = markedRight P γ hC (A ×ˢ B) := by
    intro A hA B hB
    obtain ⟨n, φ, U, hφ, hU', rfl⟩ := hA
    have hcm : MeasurableSet (cylinder φ U) := measurableSet_cylinder hφ hU'
    rw [markedLeft_prod_eq P hκs hcm hB, markedRight_prod_eq γ hG hcm hB]
    have hind0 : ∀ ω, (cylinder φ U).indicator (1 : PairFun → ℝ≥0∞) (toPairFun (hC ω)) =
        U.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) (fun j => hC ω (φ j)) := by
      intro ω
      by_cases h : (fun j => hC ω (φ j)) ∈ U
      · have h' : toPairFun (hC ω) ∈ cylinder φ U := h
        simp only [Set.indicator_of_mem h', Set.indicator_of_mem h, Pi.one_apply]
      · have h' : toPairFun (hC ω) ∉ cylinder φ U := h
        simp only [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
    have hind1 : ∀ z ω, (cylinder φ U).indicator (1 : PairFun → ℝ≥0∞)
        (toPairFun (shiftedPairing γ z (hC ω))) =
        U.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) := by
      intro z ω
      by_cases h : (fun j => hC ω (φ j) + ∫ x, dmsShift γ z x * φ j x) ∈ U
      · have h' : toPairFun (shiftedPairing γ z (hC ω)) ∈ cylinder φ U := h
        simp only [Set.indicator_of_mem h', Set.indicator_of_mem h, Pi.one_apply]
      · have h' : toPairFun (shiftedPairing γ z (hC ω)) ∉ cylinder φ U := h
        simp only [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
    simp only [hind0, hind1]
    have hΨ : Measurable (U.indicator (1 : (Fin n → ℝ) → ℝ≥0∞)) := measurable_const.indicator hU'
    have hae : ∀ᵐ ω ∂P, U.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) (fun j => hC ω (φ j)) * κ ω B =
        U.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) (fun j => hC ω (φ j)) * κ ω (B ∩ ball (0 : ℂ) 1) := by
      filter_upwards [hsupp B hB] with ω hω
      rw [hω]
    rw [lintegral_congr_ae hae]
    exact lintegral_palm_psi hG γ hμ hU hκm hκa hφ hB hΨ
  exact ext_marked_of_cylinder hcyl (hLuniv.trans hRuniv.symm)

end HarmonicBalls

end
