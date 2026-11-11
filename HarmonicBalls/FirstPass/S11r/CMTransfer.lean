import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.S11c.TranslateField11_7
import HarmonicBalls.FirstPass.S11i.RootedFrequencyShift
import HarmonicBalls.FirstPass.S11s.Event

/-!
# Cameron-Martin transfer of measurable events to the translated and shifted field


* `ae_addFunPairing_of_ae`: the generic transfer. If a measurable set `B` of distributions contains `hCz ω` almost surely,
  then `addFunPairing (hCz ω) g ∈ B` almost surely. The only input is the frozen Cameron-Martin quasi-invariance
  `CameronMartinGFFMutualAbsCont` (`FirstPass/Frozen/S11d.lean`), applied to the complement of `B`.
* `ae_canonFieldOf_addFunPairing_mem`: the same for a measurable set `G` of canonical fields, with
  `B = canonFieldOf γ ⁻¹' G`, measurable by `measurable_canonFieldOf`.
* The three instances, for the translated field `translatedPairing hC hcirc z` and the shift `g`:
  `ae_shiftedCanon_mem_regularity` (measurable decoder regularity set), `ae_shiftedCanon_mem_identification`
  (measurable canonical identification set), `ae_shiftedCanon_mem_covariance` (measurable covariance event `covEvent`,
  `FirstPass/S11s/Event.lean`). Each conclusion is `canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) g) ∈ _`,
  which is definitionally `shiftedCanon γ hC hcirc z g ω ∈ _` (`FirstPass/S11at.lean`).

The translated GFF hypothesis `IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z)` is an explicit
hypothesis. It is supplied by `isWholePlaneGFF_translatedPairing` (`FirstPass/S11ai/RootedTransfer.lean:86`) from
`AffineInvarianceAll Ω`. No new frozen or proposed input is introduced here.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Filter
open scoped ENNReal

/-- **Generic Cameron-Martin event transfer (§2.1).** Let `hCz` be a whole-plane GFF and `g` a smooth compactly
supported function with zero unit-circle average. If a measurable set `B` of distributions contains `hCz ω` almost surely,
then `addFunPairing (hCz ω) g` lies in `B` almost surely. Proof: the frozen `CameronMartinGFFMutualAbsCont` applied to `Bᶜ`. -/
theorem ae_addFunPairing_of_ae {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    {hCz : Ω → (ℂ → ℝ) → ℝ} {hcircz : Ω → ℝ → ℂ → ℝ} (hhz : IsWholePlaneGFF P hCz hcircz)
    {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcomp : HasCompactSupport g)
    (hg0 : Real.circleAverage g 0 1 = 0)
    {B : Set ((ℂ → ℝ) → ℝ)} (hB : MeasurableSet[distributionMeasurableSpace] B)
    (hbase : ∀ᵐ ω ∂P, hCz ω ∈ B) :
    ∀ᵐ ω ∂P, addFunPairing (hCz ω) g ∈ B := by
  have hzero : P ((fun ω => hCz ω) ⁻¹' Bᶜ) = 0 := ae_iff.mp hbase
  have hBc : MeasurableSet[distributionMeasurableSpace] Bᶜ := by
    let _mS : MeasurableSpace ((ℂ → ℝ) → ℝ) := distributionMeasurableSpace
    exact hB.compl
  have hiff := hCM Ω P hCz hcircz g hhz hg hcomp hg0 Bᶜ hBc
  exact ae_iff.mpr (hiff.mp hzero)

/-- **Transfer of a measurable canonical-field event (§2.1 with `B = canonFieldOf γ ⁻¹' G`).** -/
theorem ae_canonFieldOf_addFunPairing_mem {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (γ : ℝ)
    {hCz : Ω → (ℂ → ℝ) → ℝ} {hcircz : Ω → ℝ → ℂ → ℝ} (hhz : IsWholePlaneGFF P hCz hcircz)
    {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcomp : HasCompactSupport g)
    (hg0 : Real.circleAverage g 0 1 = 0)
    {G : Set S11n.CanonSpace} (hG : MeasurableSet G)
    (hbase : ∀ᵐ ω ∂P, canonFieldOf γ (hCz ω) ∈ G) :
    ∀ᵐ ω ∂P, canonFieldOf γ (addFunPairing (hCz ω) g) ∈ G :=
  ae_addFunPairing_of_ae P hCM hhz hg hcomp hg0 (measurable_canonFieldOf γ hG) hbase

/-- **Instance 1 (§2.2, `Breg`): membership in the measurable decoder regularity set.** For the translated field
`translatedPairing hC hcirc z` and the shift `g`, the shifted canonical field stays in the measurable set `Greg` almost surely,
provided it does so for the translated field. Applied with `Greg` the set `G` of the measurable decoder strengthening. -/
theorem ae_shiftedCanon_mem_regularity {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (γ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (z : ℂ)
    (hhz : IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcomp : HasCompactSupport g)
    (hg0 : Real.circleAverage g 0 1 = 0)
    {Greg : Set S11n.CanonSpace} (hGreg : MeasurableSet Greg)
    (hbase : ∀ᵐ ω ∂P, canonFieldOf γ (S11c.translatedPairing hC hcirc z ω) ∈ Greg) :
    ∀ᵐ ω ∂P, canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) g) ∈ Greg :=
  ae_canonFieldOf_addFunPairing_mem P hCM γ hhz hg hcomp hg0 hGreg hbase

/-- **Instance 2 (§2.2): membership in the measurable canonical identification set.** Same transfer, with a
measurable set `Gid` of canonical fields in place of the decoder regularity set. -/
theorem ae_shiftedCanon_mem_identification {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (γ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (z : ℂ)
    (hhz : IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcomp : HasCompactSupport g)
    (hg0 : Real.circleAverage g 0 1 = 0)
    {Gid : Set S11n.CanonSpace} (hGid : MeasurableSet Gid)
    (hbase : ∀ᵐ ω ∂P, canonFieldOf γ (S11c.translatedPairing hC hcirc z ω) ∈ Gid) :
    ∀ᵐ ω ∂P, canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) g) ∈ Gid :=
  ae_canonFieldOf_addFunPairing_mem P hCM γ hhz hg hcomp hg0 hGid hbase

/-- **Instance 3 (§2.2, `hdil`): membership in the measurable covariance event `covEvent`.** The event
`covEvent (fun L => K L) dd C Q` is measurable by `measurableSet_covEvent` (`FirstPass/S11s/Event.lean:47`). -/
theorem ae_shiftedCanon_mem_covariance {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (γ : ℝ) {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (z : ℂ)
    (hhz : IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {g : ℂ → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hcomp : HasCompactSupport g)
    (hg0 : Real.circleAverage g 0 1 = 0)
    (K : ProbabilityTheory.Kernel S11n.CanonSpace ℂ) (dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hdd : ∀ x y : ℂ, Measurable fun L => dd L x y)
    {C : Set (Set ℂ)} (hCc : C.Countable) (hCm : ∀ S ∈ C, MeasurableSet S) {Q : Set (ℂ × ℂ)} (hQ : Q.Countable)
    (hbase : ∀ᵐ ω ∂P, canonFieldOf γ (S11c.translatedPairing hC hcirc z ω) ∈ covEvent (fun L => K L) dd C Q) :
    ∀ᵐ ω ∂P, canonFieldOf γ (addFunPairing (S11c.translatedPairing hC hcirc z ω) g) ∈
      covEvent (fun L => K L) dd C Q :=
  ae_canonFieldOf_addFunPairing_mem P hCM γ hhz hg hcomp hg0
    (measurableSet_covEvent K dd hdd hCc hCm hQ) hbase

end HarmonicBalls
