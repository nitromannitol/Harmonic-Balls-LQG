import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementAssembly
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementRooted
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementConstants
import HarmonicBalls.FirstPass.Phase2.InternalMetricExitLocalization
import HarmonicBalls.FirstPass.Phase2.FixedMetricDecoderUniv

/-!
# Local agreement near every point away from the root, almost surely

Let `D ⊆ ball 0 1` be open with `0 ∉ D`, `M` a decoder on `D` (a measurable map from the mean-zero observations of `D`
to continuous functions on `D × D`) and `ρ` a test function of `D` with `∫ ρ = 1`. Every rational disk `V i` of the
cover of `Phase2/RootedLocalAgreementCover.lean` carries a normalized measurable decoder `(ρ_i, M_i)`
(`exists_diskDecoders`, from the fixed-metric decoder `localLQGMetricNormalizedMeasurableFixedMetric_derived`).

Fix a root `z`. If almost surely the reference observation of the field rooted at `z` lies in the local-agreement event
of the cover, with the distance `ofReal (M o)` and the local functions `exp(-ξ o(ρ - ρ_i)) · ofReal (M_i (o|V i))`, then
almost surely, near every point `q ≠ z` of `D`,
`ofReal (M o) = exp(-ξ (h_α(ρ) - γ ∫ log|w - z| ρ(w) dw)) · D(·,·; D)` for the internal metric of the Weyl scaling of
the LQG metric by the rooted weight `-α log|·| - γ log|· - z| + γ log max(1, |·|)`
(`ae_exists_ball_eq_mul_internalMetric_of_ae_mem_eventLocalAgreement`). The proof combines, on each of the countably
many disks with a rational margin avoiding `z`, the explicit rooted identity on the disk
(`vIdentity_rooted_weylScaling_explicit_of_margin`), the additivity of the constants
(`IsWholePlaneGFF.ae_campbellReferenceObs_meanZeroTestOfSub`) and the locality of internal metrics near the points of
the disk (`RootedLocal.internalMetric_weylScaling_eq_near`), with the deterministic assembly
`exists_ball_eq_mul_internalMetric_of_mem_eventLocalAgreement`.

Terminology: internal metric `D(·,·; U)` (Armstrong-Kuusi-Mourrat); rooted (quantum-typical) point and Weyl scaling
(Duplantier-Sheffield; Dubédat-Falconet-Gwynne-Pfeffer-Sun).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

namespace RootedLocalCover

/-- **Disk decoders.** For an LQG metric and a domain `D` not containing `0`, every rational disk of the cover of `D`
carries a normalized measurable decoder: a test function `ρ_i` of the disk with `∫ ρ_i = 1` and a measurable `M_i` with
`ofReal (M_i (h|V i)) = exp(-ξ (h, ρ_i)) · D(·,·; V i)` almost surely for every whole-plane GFF. -/
theorem exists_diskDecoders {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (h𝔇 : IsLQGMetric γ ξ 𝔇) {D : Set ℂ} (hD0 : (0 : ℂ) ∉ D) :
    ∃ (ρV : DiskIndex D → ℂ → ℝ)
      (MV : (i : DiskIndex D) → (MeanZeroTest (diskV i) → ℝ) → C(↥(diskV i ×ˢ diskV i), ℝ)),
      ∀ i, IsTestFunction (diskV i) (ρV i) ∧ ∫ x, ρV i x = 1 ∧ Measurable (MV i) ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, ∀ p : ↥(diskV i ×ˢ diskV i),
            ENNReal.ofReal (MV i (localMeanZeroObs 0 (diskV i) (hC ω)) p) =
              ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) (ρV i))) *
                internalMetric (𝔇 (hC ω)) (diskV i) p.1.1 p.1.2 := by
  have h := fun i : DiskIndex D =>
    localLQGMetricNormalizedMeasurableFixedMetric_derived.{u} γ ξ (cen i.1) (rad i.1) hγ0 hγ2 i.2.1
      (fun h0 => hD0 (i.2.2 h0)) 𝔇 h𝔇
  choose ρV MV hρV h1V hMV hid using h
  exact ⟨ρV, MV, fun i => ⟨hρV i, h1V i, hMV i, hid i⟩⟩

/-- **Local agreement near every point away from a fixed root, almost surely.** Fix `z`. If almost surely the reference
observation `o` of the field rooted at `z` lies in the local-agreement event of the rational cover of `D`, with distance
`ofReal (M o)` and local functions `exp(-ξ o(ρ - ρ_i)) · ofReal (M_i (o|V i))`, then almost surely, on a ball around every
`q ∈ D`, `q ≠ z`, `ofReal (M o) = exp(-ξ (h_α(ρ) - γ ∫ log|w - z| ρ(w) dw)) · D(·,·; D)` for the internal metric of the
Weyl scaling of the LQG metric by the rooted weight. -/
theorem ae_exists_ball_eq_mul_internalMetric_of_ae_mem_eventLocalAgreement {γ ξ α : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hCM : CameronMartinGFFMutualAbsCont.{u})
    {D : Set ℂ} (hD : IsOpen D) (hDU : D ⊆ ball (0 : ℂ) 1) (hD0 : (0 : ℂ) ∉ D)
    (M : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ)) {ρ : ℂ → ℝ} (hρ : IsTestFunction D ρ)
    (h1 : ∫ x, ρ x = 1) (ρV : DiskIndex D → ℂ → ℝ)
    (MV : (i : DiskIndex D) → (MeanZeroTest (diskV i) → ℝ) → C(↥(diskV i ×ˢ diskV i), ℝ))
    (hρV : ∀ i, IsTestFunction (diskV i) (ρV i)) (h1V : ∀ i, ∫ x, ρV i x = 1)
    (hMV : ∀ i, Measurable (MV i))
    (hid : ∀ i, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ ω ∂P, ∀ p : ↥(diskV i ×ˢ diskV i),
        ENNReal.ofReal (MV i (localMeanZeroObs 0 (diskV i) (hC ω)) p) =
          ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) (ρV i))) *
            internalMetric (𝔇 (hC ω)) (diskV i) p.1.1 p.1.2)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) (z : ℂ)
    (hA : ∀ᵐ ω ∂P, (campbellReferenceObs γ α D (hC ω) z).2 ∈ eventLocalAgreement (ratPts D)
      (fun i k => DiskAdm i k) (fun _ k => diskT k)
      (fun o u v => ENNReal.ofReal (extendDist (D ×ˢ D) (M o) u v))
      (fun i o u v =>
        ENNReal.ofReal (Real.exp (-ξ * o (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)))) *
          ENNReal.ofReal (extendDist (diskV i ×ˢ diskV i) (MV i (obsRestrict (diskV_subset i) o)) u v))) :
    ∀ᵐ ω ∂P, ∀ q ∈ D, q ≠ z → ∃ s > 0, ball q s ⊆ D ∧ ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      ENNReal.ofReal (extendDist (D ×ˢ D) (M (campbellReferenceObs γ α D (hC ω) z).2) u v) =
        ENNReal.ofReal (Real.exp (-ξ * (fieldPairing α (hC ω) ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w))) *
          internalMetric (fun a b => (weylScaling (𝔇 (hC ω)) ξ
            (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) a b).toReal)
            D u v := by
  have hD1 : ∀ w ∈ D, ‖w‖ ≤ 1 := fun w hw => (mem_ball_zero_iff.mp (hDU hw)).le
  have hdist : ∀ (i : DiskIndex D) (R : ℚ), z ∉ closedBall (cen i.1) R → (R : ℝ) < dist z (cen i.1) :=
    fun _ _ hzR => not_le.mp fun h => hzR (mem_closedBall.mpr h)
  -- the explicit rooted identity on every disk with a rational margin avoiding `z`
  have h2 : ∀ i : DiskIndex D, ∀ᵐ ω ∂P, ∀ R : ℚ, rad i.1 < R → closedBall (cen i.1) R ⊆ D →
      z ∉ closedBall (cen i.1) R → ∀ p : ↥(diskV i ×ˢ diskV i),
        ENNReal.ofReal (MV i (campbellReferenceObs γ α (diskV i) (hC ω) z).2 p) =
          ENNReal.ofReal (Real.exp (-ξ * (fieldPairing α (hC ω) (ρV i) -
            γ * ∫ w, Real.log ‖w - z‖ * ρV i w))) *
            internalMetric (fun a b => (weylScaling (𝔇 (hC ω)) ξ
              (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) a b).toReal)
              (diskV i) p.1.1 p.1.2 := by
    intro i
    by_cases hR : ∃ R : ℚ, rad i.1 < R ∧ closedBall (cen i.1) R ⊆ D ∧ z ∉ closedBall (cen i.1) R
    · obtain ⟨R, hrR, hRD, hzR⟩ := hR
      filter_upwards [vIdentity_rooted_weylScaling_explicit_of_margin hγ0 hγ2 i.2.1 h𝔇 hPhi hCM (ρV i)
        (hρV i) (MV i) (hMV i) (hid i) hrR (hdist i R hzR) (hRD.trans hDU) (fun h0 => hD0 (i.2.2 h0))
        Ω P hC hcirc hGFF] with ω hω
      exact fun _ _ _ _ => hω
    · exact Filter.Eventually.of_forall fun _ R hrR hRD hzR => (hR ⟨R, hrR, hRD, hzR⟩).elim
  -- the constants: `o(ρ - ρ_i)` is the difference of the rooted pairings
  have hk : ∀ i : DiskIndex D, ∀ᵐ ω ∂P, ∀ z : ℂ,
      (campbellReferenceObs γ α D (hC ω) z).2 (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)) =
        (fieldPairing α (hC ω) ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w) -
          (fieldPairing α (hC ω) (ρV i) - γ * ∫ w, Real.log ‖w - z‖ * ρV i w) := fun i =>
    hGFF.ae_campbellReferenceObs_meanZeroTestOfSub (diskV_subset i) hD1 hρ (hρV i) h1 (h1V i) γ α
  filter_upwards [hA, ae_all_iff.mpr h2, ae_all_iff.mpr hk, fmd_ae_metric hGFF h𝔇] with ω hAω h2ω hkω hLω
  refine exists_ball_eq_mul_internalMetric_of_mem_eventLocalAgreement hD M
    (fun i o => MV i (obsRestrict (diskV_subset i) o))
    (fun i o => ENNReal.ofReal (Real.exp (-ξ * o (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)))))
    hAω (fun _ => ENNReal.ofReal_ne_top) ?_
  intro i R hrR hRD hzR
  refine ⟨ENNReal.ofReal (Real.exp (-ξ * (fieldPairing α (hC ω) (ρV i) -
    γ * ∫ w, Real.log ‖w - z‖ * ρV i w))), ?_, h2ω i R hrR hRD hzR, ?_⟩
  · rw [hkω i z, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  · intro q hq
    obtain ⟨g, hgsm, hgcomp, -, hgz⟩ := exists_rooted_cutoff α γ i.2.1 hrR (hdist i R hzR) (hRD.trans hDU)
      (fun h0 => hD0 (i.2.2 h0))
    refine RootedLocal.internalMetric_weylScaling_eq_near hLω hgsm.continuous hgcomp (isOpen_diskV i)
      (isConnected_diskV i) (diskV_subset i) (fun w hw => ?_) hq
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp (hDU (diskV_subset i hw))
    rw [hgz w hw, max_eq_left hw1.le, Real.log_one, mul_zero, add_zero]

end RootedLocalCover

end HarmonicBalls
