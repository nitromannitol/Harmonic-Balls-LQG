import HarmonicBalls.Proofs.Sec8.CanonicalPhaseCertificate
import HarmonicBalls.Proofs.Sec8.LocalCircleDecoder

/-! # Canonical local decoders at sampled roots

The distribution-valued reconstruction and imported Section 8 arguments use
Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

open MeasureTheory Filter Set Metric ProbabilityTheory
open scoped Topology

namespace HarmonicBalls

/-- Jointly measurable observables of a cylinder process agree simultaneously
at every parameter when the processes agree almost surely in each coordinate. -/
theorem ae_forall_joint_functional_eq_of_coordinatewise_ae_eq
    {Ω ι : Type*} {Z : Type} [MeasurableSpace Ω] [MeasurableSpace Z]
    {P : Measure Ω} {X Y : Ω → ι → ℝ}
    (hxy : ∀ i, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    (D : (ι → ℝ) → Z → ℝ) (hD : Measurable (Function.uncurry D)) :
    ∀ᵐ ω ∂P, ∀ z, D (X ω) z = D (Y ω) z := by
  let F : Ω → Sum ι ι → ℝ := fun ω s => Sum.elim (X ω) (X ω) s
  let G : Ω → Sum ι ι → ℝ := fun ω s => Sum.elim (X ω) (Y ω) s
  let E : Set (Z × (Sum ι ι → ℝ)) :=
    {p | D (fun i => p.2 (.inl i)) p.1 = D (fun i => p.2 (.inr i)) p.1}
  have hE : MeasurableSet E := by
    apply measurableSet_eq_fun
    · have hm : Measurable (fun p : Z × (Sum ι ι → ℝ) =>
          (fun i => p.2 (.inl i), p.1)) := by
        exact (measurable_pi_iff.mpr fun i =>
          (measurable_pi_apply (Sum.inl i : Sum ι ι)).comp measurable_snd).prodMk measurable_fst
      exact hD.comp hm
    · have hm : Measurable (fun p : Z × (Sum ι ι → ℝ) =>
          (fun i => p.2 (.inr i), p.1)) := by
        exact (measurable_pi_iff.mpr fun i =>
          (measurable_pi_apply (Sum.inr i : Sum ι ι)).comp measurable_snd).prodMk measurable_fst
      exact hD.comp hm
  have hFG : ∀ i, (fun ω => F ω i) =ᵐ[P] (fun ω => G ω i) := by
    intro i
    cases i with
    | inl i => exact Filter.EventuallyEq.rfl
    | inr i => exact hxy i
  filter_upwards [ae_forall_mem_iff_of_coordinatewise_ae_eq hFG E hE] with ω hω z
  exact (hω z).mp rfl

/-- Every dyadic centered circle average can be decoded from a local canonical
field, simultaneously in the circle center and the dyadic scale. -/
theorem IsWholePlaneGFF.exists_canonical_local_centeredCircle_decoders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) :
    ∃ D : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      (∀ n, Measurable (Function.uncurry (D n))) ∧
      ∀ᵐ ω ∂P, ∀ n z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
        D n (fun φ => H ω φ.1.1) z =
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
            fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0 := by
  choose D hDm hDeq using fun n =>
    hGFF.exists_localPairing_centeredCircle_decoder (α₀ := α₀) (ε := ε) (dyadicScale_pos n)
  have hcan (n : ℕ) := ae_forall_joint_functional_eq_of_coordinatewise_ae_eq
    (fun (φ : Section6.LocalTest (ball 0 ε)) => hversion φ.1) (D n) (hDm n)
  refine ⟨D, hDm, ?_⟩
  filter_upwards [ae_all_iff.mpr hcan, ae_all_iff.mpr hDeq] with ω hω hω' n z hz
  exact (hω n z).trans (hω' n z hz)

/-- The same decoders represent circle averages centered at a sampled root.
The two circles are required to remain in the local field neighborhood. -/
theorem IsWholePlaneGFF.exists_rooted_canonical_local_circle_decoders
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) (κ : Kernel Ω ℂ) :
    ∃ D : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → ℂ → ℝ,
      (∀ n, Measurable (Function.uncurry (D n))) ∧
      ∀ᵐ p ∂P ⊗ₘ κ, ∀ n z,
        closedBall p.2 (dyadicScale n) ⊆ ball 0 ε →
        closedBall (z + p.2) (dyadicScale n) ⊆ ball 0 ε →
        D n (fun φ => H p.1 φ.1.1) (z + p.2) -
            D n (fun φ => H p.1 φ.1.1) p.2 =
          fieldCircleAverage α₀ (hcirc p.1) (dyadicScale n) (z + p.2) -
            fieldCircleAverage α₀ (hcirc p.1) (dyadicScale n) p.2 := by
  obtain ⟨D, hDm, hDeq⟩ :=
    hGFF.exists_canonical_local_centeredCircle_decoders (α₀ := α₀) (ε := ε) H hversion
  refine ⟨D, hDm, ?_⟩
  filter_upwards [ae_fst_of_ae_compProd P κ hDeq] with p hp n z hroot hz
  rw [hp n (z + p.2) hz, hp n p.2 hroot]
  ring

#print axioms ae_forall_joint_functional_eq_of_coordinatewise_ae_eq
#print axioms IsWholePlaneGFF.exists_canonical_local_centeredCircle_decoders
#print axioms IsWholePlaneGFF.exists_rooted_canonical_local_circle_decoders

end HarmonicBalls
