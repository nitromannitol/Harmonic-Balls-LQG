import HarmonicBalls.Proofs.Sec8.InsertedPhaseFrequencyEvent
import HarmonicBalls.Proofs.Sec8.MeanZeroDistributionVersion
import HarmonicBalls.Proofs.Sec8.RootedSamplingProbability
import Mathlib.MeasureTheory.Constructions.Cylinders

/-! # Canonical distribution and phase certificates

The distribution-valued reconstruction and the imported frequency argument
use Leonardo Bonanno's LatticeProb formalization. -/

noncomputable section

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A measurable event on a parameter and a cylinder process depends on only
countably many process coordinates, uniformly over the parameter. -/
theorem ae_forall_mem_iff_of_coordinatewise_ae_eq
    {Ω ι : Type*} {Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z] {P : Measure Ω}
    {X Y : Ω → ι → ℝ}
    (hxy : ∀ i, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    (E : Set (Z × (ι → ℝ))) (hE : MeasurableSet E) :
    ∀ᵐ ω ∂P, ∀ z, (z, X ω) ∈ E ↔ (z, Y ω) ∈ E := by
  let T : Option ι → Type := fun i => match i with | none => Z | some _ => ℝ
  let (i : Option ι) : MeasurableSpace (T i) := by
    cases i <;> dsimp [T] <;> infer_instance
  let unpack : (∀ i, T i) → Z × (ι → ℝ) := fun v => (v none, fun i => v (some i))
  have hunpack : Measurable unpack := by
    apply Measurable.prodMk
    · exact measurable_pi_apply none
    · exact measurable_pi_iff.mpr (fun i => measurable_pi_apply (some i))
  obtain ⟨I, A, hI, hA⟩ := (hE.preimage hunpack).eq_preimage_restrict_countable
  let : Countable I := hI.to_subtype
  have hcoord (i : I) : ∀ᵐ ω ∂P, match i.1 with
      | none => True
      | some j => X ω j = Y ω j := by
    cases hi : i.1 with
    | none => simp
    | some j =>
      filter_upwards [hxy j] with ω hω
      simpa only [hi] using hω
  filter_upwards [ae_all_iff.mpr hcoord] with ω hω z
  let pack (f : ι → ℝ) : ∀ i, T i := fun i =>
    match i with | none => z | some j => f j
  have heq : I.domRestrict (pack (X ω)) = I.domRestrict (pack (Y ω)) := by
    funext i
    have hi := hω i
    rcases i with ⟨i, hiI⟩
    cases i with
    | none => rfl
    | some j => exact hi
  have hmem : pack (X ω) ∈ unpack ⁻¹' E ↔ pack (Y ω) ∈ unpack ⁻¹' E := by
    rw [hA]
    change I.domRestrict (pack (X ω)) ∈ A ↔ I.domRestrict (pack (Y ω)) ∈ A
    rw [heq]
  exact hmem

/-- Coordinatewise almost-sure agreement preserves the joint law with any
measurable companion observable, even for an infinite underlying measure. -/
theorem map_prod_eq_of_coordinatewise_ae_eq
    {Ω ι : Type*} {Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {X Y : Ω → ι → ℝ} (T : Ω → Z)
    (hX : Measurable X) (hY : Measurable Y) (hT : Measurable T)
    (hxy : ∀ i, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i)) :
    P.map (fun ω => (X ω, T ω)) = P.map (fun ω => (Y ω, T ω)) := by
  ext A hA
  rw [Measure.map_apply (hX.prodMk hT) hA, Measure.map_apply (hY.prodMk hT) hA]
  have hE : MeasurableSet (Prod.swap ⁻¹' A) := hA.preimage measurable_swap
  have he := ae_forall_mem_iff_of_coordinatewise_ae_eq hxy (Prod.swap ⁻¹' A) hE
  apply measure_congr
  filter_upwards [he] with ω hω
  exact propext (hω (T ω))

/-- The canonical local field and the original local pairings have the same
joint law with every measurable companion, including a random measure or root. -/
theorem IsWholePlaneGFF.map_canonical_localPairingProd_eq
    {Ω : Type*} {Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (U : Set ℂ) (T : Ω → Z) (hT : Measurable T) :
    P.map (fun ω => (fun φ : Section6.LocalTest U => H ω φ.1.1, T ω)) =
      P.map (fun ω => (Section6.localPairingProc U hC ω, T ω)) := by
  apply map_prod_eq_of_coordinatewise_ae_eq T
  · exact measurable_pi_iff.mpr fun φ =>
      (LQGMetric.measurable_distOn_apply φ.1.1).comp hH
  · exact measurable_pi_iff.mpr fun φ =>
      hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  · exact hT
  · exact fun φ => hversion φ.1

/-- Root-dependent insertions preserve the joint law of the raw and canonical
local fields under a composition-product sampling law. -/
theorem IsWholePlaneGFF.map_rooted_canonical_localPairingProd_eq
    {Ω : Type*} {Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (U : Set ℂ) (κ : Kernel Ω Z) (s : Z → Section6.LocalTest U → ℝ)
    (hs : Measurable s) :
    (P ⊗ₘ κ).map (fun p => (fun φ : Section6.LocalTest U =>
      H p.1 φ.1.1 + s p.2 φ, p.2)) =
    (P ⊗ₘ κ).map (fun p => (fun φ : Section6.LocalTest U =>
      hC p.1 φ.1.1 + s p.2 φ, p.2)) := by
  apply map_prod_eq_of_coordinatewise_ae_eq Prod.snd
  · apply measurable_pi_iff.mpr
    intro φ
    exact (((LQGMetric.measurable_distOn_apply φ.1.1).comp hH).comp measurable_fst).add
      (((measurable_pi_apply φ).comp hs).comp measurable_snd)
  · apply measurable_pi_iff.mpr
    intro φ
    exact ((hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).comp
      measurable_fst).add (((measurable_pi_apply φ).comp hs).comp measurable_snd)
  · exact measurable_snd
  · intro φ
    filter_upwards [ae_fst_of_ae_compProd P κ (hversion φ.1)] with p hp
    exact congrArg (fun t : ℝ => t + s p.2 φ) hp

/-- On the full mean-zero cylinder process, canonical reconstruction also
preserves the joint rooted law after any measurable insertion. -/
theorem IsWholePlaneGFF.map_rooted_canonical_pairingProd_eq
    {Ω : Type*} {Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (κ : Kernel Ω Z) (s : Z → LQGMetric.TestC0 → ℝ) (hs : Measurable s) :
    (P ⊗ₘ κ).map (fun p => (fun φ : LQGMetric.TestC0 =>
      H p.1 φ.1 + s p.2 φ, p.2)) =
    (P ⊗ₘ κ).map (fun p => (fun φ : LQGMetric.TestC0 =>
      hC p.1 φ.1 + s p.2 φ, p.2)) := by
  apply map_prod_eq_of_coordinatewise_ae_eq Prod.snd
  · apply measurable_pi_iff.mpr
    intro φ
    exact (((LQGMetric.measurable_distOn_apply φ.1).comp hH).comp measurable_fst).add
      (((measurable_pi_apply φ).comp hs).comp measurable_snd)
  · apply measurable_pi_iff.mpr
    intro φ
    exact ((hh.measurable_pairing φ.1 (Section6.isTestFunction_of_testC φ.1)).comp
      measurable_fst).add (((measurable_pi_apply φ).comp hs).comp measurable_snd)
  · exact measurable_snd
  · intro φ
    filter_upwards [ae_fst_of_ae_compProd P κ (hversion φ)] with p hp
    exact congrArg (fun t : ℝ => t + s p.2 φ) hp

/-- The local phase-frequency certificate for an origin insertion remains
valid when the original field pairings are replaced by any measurable
distribution-valued version, uniformly over all phases. -/
theorem IsWholePlaneGFF.exists_canonical_inserted_phaseFrequency_event
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r →
      μ ω (ball 0 r) ≠ 0 ∧ μ ω (ball 0 r) ≠ ∞)
    (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    {R : ℝ} (hR : 0 < R)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hunit : MeasurableSet {η : Measure ℂ | IsGoodAnnulus η 1 0 a b}) :
    ∃ E : Set (PhaseTorus × (Section6.LocalTest (ball 0 R) → ℝ)),
      MeasurableSet E ∧ ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 R) =>
          H ω φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) ∈ E ↔
        ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
          ({n : ℕ | n ∈ Icc (N + 1) (2 * N) ∧
            PhaseVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
              a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
            AnnulusBallComparison (μ ω) n 0 m}.ncard : ℝ)) := by
  obtain ⟨E, hE, heq⟩ := hh.exists_inserted_phaseFrequency_event hμ hpos hR
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ hunit
  refine ⟨E, hE, ?_⟩
  have hxy (φ : Section6.LocalTest (ball 0 R)) :
      (fun ω => H ω φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) =ᵐ[P]
      (fun ω => hC ω φ.1.1 + ∫ x, φ.1.1 x * (-α * Real.log ‖x‖)) := by
    filter_upwards [hversion φ.1] with ω hω
    rw [hω]
  have hEeq := ae_forall_mem_iff_of_coordinatewise_ae_eq hxy E hE
  filter_upwards [heq, hEeq] with ω hω he t
  exact (he t).trans (hω t)

#print axioms ae_forall_mem_iff_of_coordinatewise_ae_eq
#print axioms map_prod_eq_of_coordinatewise_ae_eq
#print axioms IsWholePlaneGFF.map_canonical_localPairingProd_eq
#print axioms IsWholePlaneGFF.map_rooted_canonical_localPairingProd_eq
#print axioms IsWholePlaneGFF.map_rooted_canonical_pairingProd_eq
#print axioms IsWholePlaneGFF.exists_canonical_inserted_phaseFrequency_event

end HarmonicBalls
