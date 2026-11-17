import HarmonicBalls.Proofs.GFF.DMSInsertedMarkedMeasureTransfer
import HarmonicBalls.FirstPass.S11i.Step8TransferMarked

/-!
# Marked local event transfer for singular Liouville measure

A shifted local-field event transfers to almost every root of the singular measure.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open ProbabilityTheory (Kernel IsFiniteKernel)

namespace HarmonicBalls

universe u

/-- The singular-measure mass of a measurable local marked event is almost surely measurable. -/
theorem IsWholePlaneGFF.aemeasurable_singular_local_marked_failure
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (U : Set ℂ) (S : Set (ModConstTestPairings U × ℂ)) (hS : MeasurableSet S) :
    AEMeasurable (fun ω => ∫⁻ z in ball (0 : ℂ) 1,
      Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (localModConstField α hC U ω, z) ∂(μ ω)) P := by
  classical
  have hAEM : AEMeasurable μ P := hh.aemeasurable_lqgMeasure hμ
  let μ' : Ω → Measure ℂ := hAEM.mk μ
  have hμ'm : Measurable μ' := hAEM.measurable_mk
  have hae : ∀ᵐ ω ∂P, μ ω = μ' ω := hAEM.ae_eq_mk
  have hfin : ∀ᵐ ω ∂P, μ ω (ball (0 : ℂ) 1) < ⊤ := by
    have h' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
    filter_upwards [h'] with ω hω
    have := hω.isLocallyFiniteMeasure
    exact measure_ball_lt_top
  have hx : Measurable fun ω => μ' ω (ball (0 : ℂ) 1) :=
    (Measure.measurable_coe measurableSet_ball).comp hμ'm
  have hc : Measurable fun ω => (1 + μ' ω (ball (0 : ℂ) 1))⁻¹ :=
    (measurable_const.add hx).inv
  let ν : Ω → Measure ℂ := fun ω => (1 + μ' ω (ball (0 : ℂ) 1))⁻¹ •
    (μ' ω).restrict (ball (0 : ℂ) 1)
  have hν : Measurable ν := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [ν, Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
    exact hc.mul ((Measure.measurable_coe (hs.inter measurableSet_ball)).comp hμ'm)
  let κ : Kernel Ω ℂ := ⟨ν, hν⟩
  have hbound : ∀ ω, κ ω Set.univ ≤ 1 := fun ω => by
    show ((1 + μ' ω (ball (0 : ℂ) 1))⁻¹ •
      (μ' ω).restrict (ball (0 : ℂ) 1)) Set.univ ≤ 1
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact FirstPassS11iStep8Transfer.inv_one_add_mul_le_one _
  have : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, hbound⟩⟩
  have hlocal : Measurable (localModConstField α hC U) := by
    have hm := (measurable_localModConstField_pairing U).comp
      (FirstPassS11iStep8Transfer.measurable_hC_pairingUniv hh)
    have hi := (measurable_localLogInsertion α U).comp hm
    convert hi using 1
    funext ω φ
    simp [localLogInsertion, localModConstField, fieldPairing]
  have hF : Measurable fun p : Ω × ℂ =>
      Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (localModConstField α hC U p.1, p.2) :=
    (measurable_const.indicator hS.compl).comp ((hlocal.comp measurable_fst).prodMk measurable_snd)
  have hH : Measurable fun ω => ∫⁻ z,
      Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (localModConstField α hC U ω, z) ∂(κ ω) :=
    hF.lintegral_kernel_prod_right' (κ := κ)
  have heq : (fun ω => ∫⁻ z in ball (0 : ℂ) 1,
      Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (localModConstField α hC U ω, z) ∂(μ ω))
      =ᵐ[P] fun ω => (1 + μ' ω (ball (0 : ℂ) 1)) * ∫⁻ z,
        Sᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (localModConstField α hC U ω, z) ∂(κ ω) := by
    filter_upwards [hae, hfin] with ω h1 h2
    rw [h1] at h2 ⊢
    have ha0 : (1 + μ' ω (ball (0 : ℂ) 1)) ≠ 0 := (zero_lt_one.trans_le le_self_add).ne'
    have haT : (1 + μ' ω (ball (0 : ℂ) 1)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, h2.ne⟩
    have hκ : κ ω = (1 + μ' ω (ball (0 : ℂ) 1))⁻¹ •
        (μ' ω).restrict (ball (0 : ℂ) 1) := rfl
    rw [hκ, lintegral_smul_measure, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel ha0 haT, one_mul]
  exact ((measurable_const.add hx).mul hH).aemeasurable.congr heq.symm

/-- A shifted-law local event holds at singular-measure almost every root in the unit ball. -/
theorem IsWholePlaneGFF.ae_singular_local_marked_of_ae_shifted
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν) (U : Set ℂ)
    (S : Set (ModConstTestPairings U × ℂ)) (hS : MeasurableSet S)
    (hshift : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P, (localModConstField α (fun _ : Unit => shiftedPairing γ z (hC ω)) U (), z) ∈ S) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 →
      (localModConstField α hC U ω, z) ∈ S := by
  classical
  let F : ModConstTestPairings U × ℂ → ℝ≥0∞ := Sᶜ.indicator (fun _ => 1)
  have hF : Measurable F := measurable_const.indicator hS.compl
  have hR : (∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖z‖ ^ (-(γ * α))) * ∫⁻ ω,
      F (localModConstField α (fun _ : Unit => shiftedPairing γ z (hC ω)) U (), z) ∂P ∂volume) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    change ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
      ENNReal.ofReal (‖z‖ ^ (-(γ * α))) * (∫⁻ ω,
        F (localModConstField α (fun _ : Unit => shiftedPairing γ z (hC ω)) U (), z) ∂P) = 0
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [hshift] with z hz hzball
    have hzero : ∫⁻ ω, F (localModConstField α
        (fun _ : Unit => shiftedPairing γ z (hC ω)) U (), z) ∂P = 0 := by
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards [hz hzball] with ω hω
      exact Set.indicator_of_notMem (by simpa using hω) _
    simp [hzero]
  have hL := (hh.lintegral_singular_inserted_localModConstField_marked hγ hγ2 hα hμ hν U F hF).trans hR
  have hG := (lintegral_eq_zero_iff' (hh.aemeasurable_singular_local_marked_failure hμ U S hS)).1 hL
  filter_upwards [hG] with ω hω
  have hmz : Measurable fun z : ℂ => F (localModConstField α hC U ω, z) :=
    hF.comp (measurable_const.prodMk measurable_id)
  have hz0 := (lintegral_eq_zero_iff' hmz.aemeasurable).1 hω
  change ∀ᵐ z ∂((μ ω).restrict (ball (0 : ℂ) 1)),
    F (localModConstField α hC U ω, z) = 0 at hz0
  rw [ae_restrict_iff' measurableSet_ball] at hz0
  filter_upwards [hz0] with z hz hzball
  by_contra hnot
  have h1 : F (localModConstField α hC U ω, z) = 1 := Set.indicator_of_mem hnot _
  exact one_ne_zero (h1.symm.trans (hz hzball))

end HarmonicBalls
