import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementUnrooted
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementUnrootedConcrete

/-!
# The unrooted observation lies almost surely in the concrete event: wiring of the decoder identities

`UnrootedLocal.ae_localMeanZeroObs_mem_eventA_ball` instantiates
`UnrootedLocal.ae_localMeanZeroObs_mem_eventA` on a disk `D = B(c, r)` whose closure avoids the origin:

* the explicit unrooted identities (18) for `D` and for the rational disks `V i` come from
  `unrooted_identity_fixedMetric_explicit` and the decoders at `α = 0`;
* the Euclidean length metric hypothesis on the Weyl-scaled metric of the field `h - α log |·|` is part I of
  `LQGMetricFieldAxioms`;
* the exhaustion of `D` by compact sets is `n ↦ closedBall c (r - r/(n+2))`.

Terminology: internal metric (Armstrong-Kuusi-Mourrat); Euclidean length metric (Gwynne-Miller); whole-plane GFF
and LQG metric (Duplantier-Sheffield, Gwynne-Miller).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace UnrootedLocal

open RootedLocalCover

/-- **The unrooted observation of the field `h - α log |·|` lies almost surely in the concrete event of the rational
cover of a disk.** The decoders `(ρ, M)` of `B(c, r)` and `(ρ_i, M_i)` of the rational disks `V i ⊆ B(c, r)`
satisfy the identities (18) at `α = 0`; then for every `α < Q`, almost surely `localMeanZeroObs α D h` lies in the
event whose distance is `M` and whose local functions are `exp(-ξ ⟨o, ρ - ρ_i⟩) · M_i (o|_{V i})`. -/
theorem ae_localMeanZeroObs_mem_eventA_ball {γ ξ : ℝ}
    (hCM : CameronMartinGFFMutualAbsCont.{u})
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hFA : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : (0 : ℂ) ∉ closedBall c r)
    {ρ : ℂ → ℝ} (hρ : IsTestFunction (ball c r) ρ) (h1 : ∫ x, ρ x = 1)
    {M : (MeanZeroTest (ball c r) → ℝ) → C(↥(ball c r ×ˢ ball c r), ℝ)} (hMm : Measurable M)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ p : ↥(ball c r ×ˢ ball c r),
          ENNReal.ofReal (M (localMeanZeroObs 0 (ball c r) (hC ω)) p) =
            ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
              internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2)
    {ρV : DiskIndex (ball c r) → ℂ → ℝ} (hρV : ∀ i, IsTestFunction (diskV i) (ρV i))
    (h1V : ∀ i, ∫ x, ρV i x = 1)
    {MV : (i : DiskIndex (ball c r)) → (MeanZeroTest (diskV i) → ℝ) → C(↥(diskV i ×ˢ diskV i), ℝ)}
    (hMV : ∀ i, Measurable (MV i))
    (hidV : ∀ i, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ p : ↥(diskV i ×ˢ diskV i),
          ENNReal.ofReal (MV i (localMeanZeroObs 0 (diskV i) (hC ω)) p) =
            ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) (ρV i))) *
              internalMetric (𝔇 (hC ω)) (diskV i) p.1.1 p.1.2)
    {α : ℝ} (hα : α < lqgQ γ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ ω ∂P, localMeanZeroObs α (ball c r) (hC ω) ∈
      eventA (ratPts (ball c r)) (fun n : ℕ => closedBall c (r - r / ((n : ℝ) + 2)))
        (fun i k => DiskAdm i k) (fun _ k => diskT k)
        (fun o u v => ENNReal.ofReal (extendDist (ball c r ×ˢ ball c r) (M o) u v))
        (fun i o u v =>
          ENNReal.ofReal (Real.exp (-ξ * o (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)))) *
            ENNReal.ofReal
              (extendDist (diskV i ×ˢ diskV i) (MV i (obsRestrict (diskV_subset i) o)) u v)) := by
  have hF : ∀ᵐ ω ∂P, IsEuclideanLengthMetric
      (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal) := by
    have hI := hFA α hα Ω P hC hcirc hGFF hγ0 hγ2 hα 𝔇 h𝔇
    exact hI.1.mono fun ω h => h.2
  have hMD := unrooted_identity_fixedMetric_explicit hCM hPhi hFA hγ0 hγ2 hr h0 h𝔇 hρ hMm hid
    α hα Ω P hC hcirc hGFF
  have hMVi : ∀ i : DiskIndex (ball c r), ∀ᵐ ω ∂P, ∀ p : ↥(diskV i ×ˢ diskV i),
      ENNReal.ofReal (MV i (localMeanZeroObs α (diskV i) (hC ω)) p) =
        ENNReal.ofReal (Real.exp (-ξ * fieldPairing α (hC ω) (ρV i))) *
          internalMetric (fun u v => (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) u v).toReal)
            (diskV i) p.1.1 p.1.2 := by
    intro i
    have h0i : (0 : ℂ) ∉ closedBall (cen i.1) (rad i.1) := fun h0' =>
      h0 (ball_subset_closedBall (i.2.2 h0'))
    exact unrooted_identity_fixedMetric_explicit hCM hPhi hFA hγ0 hγ2 i.2.1 h0i h𝔇 (hρV i) (hMV i)
      (hidV i) α hα Ω P hC hcirc hGFF
  exact ae_localMeanZeroObs_mem_eventA hGFF isOpen_ball
    ((convex_ball c r).isPathConnected (nonempty_ball.2 hr))
    (fun C hC' hCD => exists_closedBall_of_isCompact_subset_ball hC' hCD) hF α ξ hρ h1 hρV h1V M MV hMD hMVi

end UnrootedLocal

end HarmonicBalls
