import HarmonicBalls.FirstPass.Phase2.B2ShiftedProfileDecoder
import HarmonicBalls.FirstPass.Phase2.ProfileDecoderDerived
import HarmonicBalls.FirstPass.S11at.Producers

/-! # B2 shifted-profile decoder, part 2 (MQ-lh-15 steps 3 and 5)

Task `fp-phase2-b2-shifted-decoder-steps-3-5-6`, worker z3.

* `ae_canonicalSel_posPart_eq_field`: the canonical selector (`canonicalProfileSelector`, step 3) returns the field's own
  continuous profile on the positive part of the field, almost surely (from `IsWholePlaneGFF.ae_continuousOn_circle`).
* `shifted_profile_decoder_limit_ae_root`: step 4 for the true shifted profile. For Lebesgue-a.e. root `z`, almost surely,
  every continuous profile `y` equal to the positive part of the DMS-shifted circle profile lies in `convSet T γ 0` and has
  the LQG limit `decoder T γ 0 y`.
* `shifted_rootedLQGMeasure_ae_exists`: step 5, `FirstPassS11atProducers.ae_exists_rootedLQGMeasure_derived` with its
  premise `hProf` discharged by the binder-free `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (lead ruling).
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal
open FirstPassS11atProducers

namespace HarmonicBalls

universe u

/-- The canonical selector returns the continuous profile of the field on the positive part, almost surely (step 3):
for a.e. `ω`, `posPart (hcirc ω)` is the zero extension of the continuous profile `p ↦ hcirc ω p.1 p.2`, and `Sel`
recovers that profile. -/
theorem ae_canonicalSel_posPart_eq_field {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (Sel : (ℝ → ℂ → ℝ) → C(CircleParameter, ℝ))
    (hRec : ∀ y : C(CircleParameter, ℝ), Sel (posExtend ⇑y) = y) :
    ∀ᵐ ω ∂P, ∀ p : CircleParameter, Sel (posPart (hcirc ω)) p = hcirc ω p.1 p.2 := by
  filter_upwards [hGFF.ae_continuousOn_circle] with ω hω
  have hc : Continuous (fun p : CircleParameter => hcirc ω p.1 p.2) :=
    hω.comp_continuous ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      fun p => Set.mk_mem_prod p.1.2 (Set.mem_univ _)
  have h2 : Sel (posPart (hcirc ω)) = ⟨fun p : CircleParameter => hcirc ω p.1 p.2, hc⟩ := by
    rw [← posExtend_coe_eq (hcirc ω)]
    exact hRec ⟨fun p : CircleParameter => hcirc ω p.1 p.2, hc⟩
  intro p
  rw [h2]
  rfl

/-- **Step 4 for the true shifted profile (MQ-lh-15, with the step-3 canonical selector).** For Lebesgue-a.e. root `z` in
the unit ball, almost surely: whenever the positive part of the DMS-shifted circle profile is the zero extension of a
continuous profile `y`, `y` lies in the convergence locus `convSet T γ 0` and its LQG limit is `decoder T γ 0 y`.
Given the candidate joint identity `hJoint` (PENDING R26) as a hypothesis; no other hypothesis. -/
theorem shifted_profile_decoder_limit_ae_root
    (hJoint : DMSLemmaA10WholePlaneMarkedJointPosStmt.{u})
    (T : ProfileDecoderDerived.TestFamily) (γ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P, ∀ y : C(CircleParameter, ℝ),
      posPart (dmsShiftedCircle γ z (hcirc ω)) = posExtend ⇑y →
        y ∈ ProfileDecoderDerived.convSet T γ 0 ∧
          IsLQGLimit γ (fieldCircleAverage 0 (circleProfile y)) (ProfileDecoderDerived.decoder T γ 0 y) := by
  obtain ⟨Sel, hSelM, hRec⟩ := canonicalProfileSelector
  have hagree := ae_canonicalSel_posPart_eq_field hGFF Sel hRec
  have hSelAe : ∀ p : CircleParameter, (fun ω => Sel (posPart (hcirc ω)) p) =ᵐ[P] fun ω => hcirc ω p.1 p.2 :=
    fun p => hagree.mono fun ω hω => hω p
  have hmain := shifted_selected_mem_convSet_ae_root hJoint T γ hγ0 hγ2 P hC hcirc μ hGFF hμ Sel hSelM hSelAe
  filter_upwards [hmain] with z hz
  filter_upwards [hz] with ω hω
  intro y hy
  have hSy : Sel (posPart (dmsShiftedCircle γ z (hcirc ω))) = y := by
    rw [hy]
    exact hRec y
  rw [hSy] at hω
  exact ⟨hω, ProfileDecoderDerived.isLQGLimit_decoder T γ 0 hω⟩

/-- **Step 5 (MQ-lh-15 route).** `FirstPassS11atProducers.ae_exists_rootedLQGMeasure_derived` with its premise `hProf`
discharged by the binder-free `HarmonicBalls.lqgMeasureOfProfileMeasurable_derived` (lead ruling, standing delegation).
The remaining premises `hExist0`, `hExistα`, `hA10` are those of the producer, not discharged here. -/
theorem shifted_rootedLQGMeasure_ae_exists {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ : ℂ) (r₁ : ℝ)
    (hh : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ) (hWin : ball c₁ r₁ ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleFieldP α₀ γ hcirc z) μz :=
  FirstPassS11atProducers.ae_exists_rootedLQGMeasure_derived P γ α₀ hC hcirc c₁ r₁ hh hγ0 hγ2 hα hExist0 hExistα hA10
    lqgMeasureOfProfileMeasurable_derived hWin

/-- **Step 5, subcritical form (MQ-lh-15, operator item (1)).** Same statement as `shifted_rootedLQGMeasure_ae_exists`,
with the universally typed marked input `hA10` replaced by its subcritical form
`hSub : ∀ μ, DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ` (`FirstPass/Frozen/S11i.lean:59`), whose statement carries the
range `0 < γ`, `γ < 2`. At the given `γ`, the marked form is recovered by `dmsA10Marked_of_sub` (`S11i.lean:69`) from
`hγ0`, `hγ2`. The old theorem `shifted_rootedLQGMeasure_ae_exists` is kept unchanged (no own downstream use of it exists). -/
theorem shifted_rootedLQGMeasure_ae_exists_sub {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (c₁ : ℂ) (r₁ : ℝ)
    (hh : IsWholePlaneGFF P hC hcirc) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hSub : ∀ μ : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarkedSub P γ hC hcirc μ) (hWin : ball c₁ r₁ ⊆ ball (0 : ℂ) 1) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (rootedCircleFieldP α₀ γ hcirc z) μz :=
  shifted_rootedLQGMeasure_ae_exists P γ α₀ hC hcirc c₁ r₁ hh hγ0 hγ2 hα hExist0 hExistα
    (fun μ => dmsA10Marked_of_sub P γ hC hcirc μ (hSub μ) hγ0 hγ2) hWin

end HarmonicBalls
