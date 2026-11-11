import HarmonicBalls.Proofs.Sec8.LocalCircleDecoder
import HarmonicBalls.Proofs.Sec8.AEMassRatioRepresentatives
import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import HarmonicBalls.Proofs.Sec8.TranslatedDistributionMeasurable

/-! # Canonical local normalized approximations

The distribution-valued reconstruction is from Leonardo Bonanno's LatticeProb
formalization. -/

noncomputable section

open MeasureTheory Filter Set Metric

namespace HarmonicBalls

/-- A measurable functional cannot distinguish two processes which agree
almost surely in each coordinate, even when their exceptional sets vary. -/
theorem ae_measurable_functional_eq_of_coordinatewise_ae_eq
    {Ω ι E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] [MeasurableEq E]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → ι → ℝ}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ i, (fun ω => X ω i) =ᵐ[P] (fun ω => Y ω i))
    (f : (ι → ℝ) → E) (hf : Measurable f) :
    (fun ω => f (X ω)) =ᵐ[P] (fun ω => f (Y ω)) := by
  let F : Ω → Sum ι ι → ℝ := fun ω s => Sum.elim (X ω) (X ω) s
  let G : Ω → Sum ι ι → ℝ := fun ω s => Sum.elim (X ω) (Y ω) s
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | inl i => exact (measurable_pi_apply i).comp hX
    | inr i => exact (measurable_pi_apply i).comp hX
  have hG : Measurable G := by
    apply measurable_pi_iff.mpr
    intro i
    cases i with
    | inl i => exact (measurable_pi_apply i).comp hX
    | inr i => exact (measurable_pi_apply i).comp hY
  have heq : P.map F = P.map G := by
    apply map_pi_eq_of_coordinatewise_ae_eq hF hG
    intro i
    cases i with
    | inl i => exact Filter.EventuallyEq.rfl
    | inr i => exact h i
  let A : Set (Sum ι ι → ℝ) := {v | f (fun i => v (.inl i)) = f (fun i => v (.inr i))}
  have hA : MeasurableSet A := by
    apply measurableSet_eq_fun
    · apply hf.comp
      exact measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i : Sum ι ι)
    · apply hf.comp
      exact measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inr i : Sum ι ι)
  have hfull : ∀ᵐ v ∂P.map F, v ∈ A := by
    apply (ae_map_iff hF.aemeasurable hA).2
    exact Filter.Eventually.of_forall fun _ => rfl
  rw [heq] at hfull
  exact (ae_map_iff hG.aemeasurable hA).1 hfull

/-- A distribution-valued version recovers the masses of the local normalized
LQG approximations on any countable family of measurable sets, simultaneously. -/
theorem IsWholePlaneGFF.exists_canonical_local_normalizedLQGApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (E A : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hAm : ∀ k, MeasurableSet (A k))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧ ∀ᵐ ω ∂P, ∀ n k,
        F n (fun φ => H ω φ.1.1) (A k) =
          normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
            (dyadicScale n)) (E n) (A k) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨F, hFm, hFeq⟩ := hGFF.exists_localPairing_normalizedLQGApprox
    (γ := γ) (α₀ := α₀) E hEm hbuffer
  have hlocal : Measurable (fun ω (φ : Section6.LocalTest (ball 0 ε)) => H ω φ.1.1) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (LQGMetric.measurable_distOn_apply φ.1.1).comp hH
  have hraw : Measurable (Section6.localPairingProc (ball 0 ε) hC) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact hGFF.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)
  have heq (n k : ℕ) :
      (fun ω => F n (fun φ => H ω φ.1.1) (A k)) =ᵐ[P]
        (fun ω => F n (Section6.localPairingProc (ball 0 ε) hC ω) (A k)) :=
    ae_measurable_functional_eq_of_coordinatewise_ae_eq hlocal hraw
      (fun φ => hversion φ.1) (fun x => F n x (A k))
      ((Measure.measurable_coe (hAm k)).comp (hFm n))
  refine ⟨F, hFm, ?_⟩
  filter_upwards [hFeq, ae_all_iff.mpr (fun n => ae_all_iff.mpr (heq n))] with ω hω hω' n k
  rw [hω' n k, hω n]

/-- The canonical distribution reconstructs the entire buffered normalized
approximating measures on one event, simultaneously at every dyadic scale. -/
theorem IsWholePlaneGFF.exists_canonical_local_normalizedLQGApprox_measure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) :
    ∃ F : ℕ → (Section6.LocalTest (ball 0 ε) → ℝ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧ ∀ᵐ ω ∂P, ∀ n,
        F n (fun φ => H ω φ.1.1) =
          normalizedRestriction (lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
            (dyadicScale n)) (E n) := by
  obtain ⟨S, hcount, hpi, hopen, huniv, hgen⟩ := exists_countable_open_piSystem_complex
  obtain ⟨A, hA⟩ := hcount.exists_eq_range ⟨univ, huniv⟩
  have hAm (k : ℕ) : MeasurableSet (A k) := hopen _ (hA.symm ▸ mem_range_self k) |>.measurableSet
  obtain ⟨F, hFm, heq⟩ := hGFF.exists_canonical_local_normalizedLQGApprox
    H hH hversion E A hEm hAm hbuffer
  refine ⟨F, hFm, ?_⟩
  filter_upwards [heq] with ω hω n
  let μ := lqgApprox γ (fieldCircleAverage α₀ (hcirc ω)) (dyadicScale n)
  have : IsFiniteMeasure (normalizedRestriction μ (E n)) := by
    change IsFiniteMeasure ((normalizedRestrictionKernel (E n) (hEm n)) μ)
    infer_instance
  symm
  apply ext_of_generate_finite S hgen hpi
  · intro V hV
    obtain ⟨k, rfl⟩ : V ∈ range A := hA ▸ hV
    exact (hω n k).symm
  · obtain ⟨k, hk⟩ : univ ∈ range A := hA ▸ huniv
    simpa only [hk] using (hω n k).symm

end HarmonicBalls
