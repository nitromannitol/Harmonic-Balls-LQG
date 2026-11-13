import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementESide
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementChains
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementCover
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementUnrootedWiring
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementAssemblyAE
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementTransfer
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementNear
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.S11r.Frozen
import LatticeProb.Topology.LocalAgreementDense

/-!
# Gluing a measurable decoder to the rooted internal metric of a disk

Let `D = ball c r` with `closedBall c r ⊆ ball 0 1` and `0 ∉ closedBall c r`, `d` a Euclidean length metric, `z ∈ D`,
and `E = internalMetric (weylPhysicalE d ξ k) D` the internal metric of the Weyl scaling of `d` by the rooted weight
`k = -α log|·| - γ log|· - z| + γ log max(1, |·|)`. Suppose the Weyl scaling tends to `0` at `z`. A function `d₁` on
pairs of points that is continuous on `D × D`, satisfies the diagonal, symmetry and triangle conditions and has fine
chains at the pairs of the rational points `S` of `D`, and that agrees with `b * E` (`b < ∞`) near every point of
`D \ {z}`, equals `b * E` on all of `D × D`
(`RootedLocalCover.eq_rootedInternal_of_dense_agreement`, by the dense gluing lemma for local agreement).
`RootedLocalCover.eq_rootedInternal_of_mem_eventA` states the same for a point `o` of the measurable event `A` of the
rational cover: the three conditions on `S` are the components `A1`, `A2` of `o ∈ A`.

Terminology: internal metric (Armstrong-Kuusi-Mourrat); Weyl scaling and rooted (quantum-typical) point
(Duplantier-Sheffield; Dubédat-Falconet-Gwynne-Pfeffer-Sun).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

universe u

namespace RootedLocalCover

/-- **Dense gluing of a decoder to the rooted internal metric.** -/
theorem eq_rootedInternal_of_dense_agreement {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (ξ α γ : ℝ) {c z : ℂ} {r : ℝ} (hcD : closedBall c r ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r)
    (hz : z ∈ ball c r)
    (hW : Tendsto (fun x => weylScaling d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) x z) (𝓝 z) (𝓝 0))
    {d₁ : ℂ → ℂ → ℝ≥0∞}
    (hd₁ : ContinuousOn (fun p : ℂ × ℂ => d₁ p.1 p.2) (ball c r ×ˢ ball c r))
    (hdiag₁ : ∀ x ∈ ratPts (ball c r), d₁ x x = 0)
    (hsymm₁ : ∀ x ∈ ratPts (ball c r), ∀ y ∈ ratPts (ball c r), d₁ x y = d₁ y x)
    (htri₁ : ∀ x ∈ ratPts (ball c r), ∀ y ∈ ratPts (ball c r), ∀ w ∈ ratPts (ball c r),
      d₁ x w ≤ d₁ x y + d₁ y w)
    (hch₁ : ∀ x ∈ ratPts (ball c r), ∀ y ∈ ratPts (ball c r),
      LatticeProb.Topology.HasFineChainsAt (ball c r) d₁ x y)
    {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hloc : ∀ q ∈ ball c r, q ≠ z → ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      d₁ u v = b * internalMetric (fun a b' => (weylScaling d ξ
        (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) a b').toReal)
          (ball c r) u v) :
    ∀ x ∈ ball c r, ∀ y ∈ ball c r, d₁ x y = b * internalMetric (fun a b' => (weylScaling d ξ
        (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) a b').toReal)
          (ball c r) x y := by
  have hSD : ratPts (ball c r) ⊆ ball c r := ratPts_subset _
  exact LatticeProb.Topology.eqOn_of_local_agreement_of_dense hz hSD (subset_closure_ratPts isOpen_ball)
    (d₂ := fun u v => b * internalMetric (weylPhysicalE d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) (ball c r) u v)
    hd₁ hdiag₁ hsymm₁ htri₁ hch₁
    (RootedLocal.rootedInternal_triangle hd ξ α γ h0 hz hW b)
    (RootedLocal.rootedInternal_symm hd ξ _ (ball c r) b)
    (RootedLocal.rootedInternal_diag hd ξ α γ hcD h0 hz hW hb)
    (fun x hx y hy => RootedLocal.rootedInternal_fineChainsAt _ c r hb x (hSD hx) y (hSD hy))
    hloc

/-- **Dense gluing for a point of the event `A` of the rational cover.** The conditions of the gluing on the rational
points are the components `A1` (diagonal, symmetry, triangle) and `A2` (chains with compact windows `K n ⊆ D`) of
`o ∈ A`. -/
theorem eq_rootedInternal_of_mem_eventA {Ω : Type*} [MeasurableSpace Ω] {ι κ : Type*}
    {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (ξ α γ : ℝ) {c z : ℂ} {r : ℝ} (hcD : closedBall c r ⊆ ball (0 : ℂ) 1) (h0 : (0 : ℂ) ∉ closedBall c r)
    (hz : z ∈ ball c r)
    (hW : Tendsto (fun x => weylScaling d ξ
      (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) x z) (𝓝 z) (𝓝 0))
    {K : ℕ → Set ℂ} (hKc : ∀ n, IsCompact (K n)) (hKD : ∀ n, K n ⊆ ball c r)
    {adm : ι → κ → Prop} {T : ι → κ → Set ℂ} {dd : Ω → ℂ → ℂ → ℝ≥0∞} {F : ι → Ω → ℂ → ℂ → ℝ≥0∞} {o : Ω}
    (ho : o ∈ eventA (ratPts (ball c r)) K adm T dd F)
    (hd₁ : ContinuousOn (fun p : ℂ × ℂ => dd o p.1 p.2) (ball c r ×ˢ ball c r))
    {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hloc : ∀ q ∈ ball c r, q ≠ z → ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      dd o u v = b * internalMetric (fun a b' => (weylScaling d ξ
        (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) a b').toReal)
          (ball c r) u v) :
    ∀ x ∈ ball c r, ∀ y ∈ ball c r, dd o x y = b * internalMetric (fun a b' => (weylScaling d ξ
        (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) a b').toReal)
          (ball c r) x y := by
  obtain ⟨⟨⟨⟨hdiag, hsymm⟩, htri⟩, hchain⟩, -⟩ := ho
  exact eq_rootedInternal_of_dense_agreement hd ξ α γ hcD h0 hz hW hd₁ hdiag hsymm htri
    (fun x hx y hy => chains_of_eventChains hKc hKD hchain hx hy) hb hloc

/-- **The rooted clause (20) for a decoder of a disk, almost surely.** Let `(ρ, M)` be the decoder of `D = B(c₂, r₂)` and
`(ρ_i, M_i)` the decoders of its rational disks, satisfying the unrooted identities (18) at `α = 0`, and let
`closedBall c₂ r₂ ⊆ B(0, 1)` avoid the origin. Then for Lebesgue-almost every root `z` in `U = B(c₁, r₁)`, almost
surely the decoder at the rooted observation is a positive multiple of the internal metric on `D` of the Weyl scaling of
the LQG metric by the rooted weight `-α log|·| - γ log|· - z| + γ log max (1, |·|)`. -/
theorem ae_rooted_clause_of_decoders {γ ξ α : ℝ}
    (hI1 : LocalMarkedRootingIdentityWeightedFrozen.{u})
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hPhi : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hFA : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α hC hcirc)
    (hlen : LQGMetricLengthUnivFrozen.{u}) (hins : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (hME : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (hDU : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {ρ : ℂ → ℝ} (hρ : IsTestFunction (ball c₂ r₂) ρ) (h1 : ∫ x, ρ x = 1)
    {M : (MeanZeroTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂), ℝ)} (hMm : Measurable M)
    (hid : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
          ENNReal.ofReal (M (localMeanZeroObs 0 (ball c₂ r₂) (hC ω)) p) =
            ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) ρ)) *
              internalMetric (𝔇 (hC ω)) (ball c₂ r₂) p.1.1 p.1.2)
    {ρV : DiskIndex (ball c₂ r₂) → ℂ → ℝ} (hρV : ∀ i, IsTestFunction (diskV i) (ρV i))
    (h1V : ∀ i, ∫ x, ρV i x = 1)
    {MV : (i : DiskIndex (ball c₂ r₂)) → (MeanZeroTest (diskV i) → ℝ) → C(↥(diskV i ×ˢ diskV i), ℝ)}
    (hMV : ∀ i, Measurable (MV i))
    (hidV : ∀ i, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, ∀ p : ↥(diskV i ×ˢ diskV i),
          ENNReal.ofReal (MV i (localMeanZeroObs 0 (diskV i) (hC ω)) p) =
            ENNReal.ofReal (Real.exp (-ξ * fieldPairing 0 (hC ω) (ρV i))) *
              internalMetric (𝔇 (hC ω)) (diskV i) p.1.1 p.1.2)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
        ENNReal.ofReal (M (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric
            (fun u v => (weylScaling (𝔇 (hC ω)) ξ
              (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
            (ball c₂ r₂) p.1.1 p.1.2 := by
  -- step 5: the unrooted observation lies almost surely in the concrete event `A`
  have hmem := UnrootedLocal.ae_localMeanZeroObs_mem_eventA_ball hCM hPhi hFA hγ0 hγ2 h𝔇 hr₂ h0 hρ h1 hMm
    hid hρV h1V hMV hidV hα Ω P hC hcirc hGFF
  -- step 4: `A` is measurable
  have hAmeas := measurableSet_eventA (Ω := MeanZeroTest (ball c₂ r₂) → ℝ) (countable_ratPts (ball c₂ r₂))
    (fun n : ℕ => closedBall c₂ (r₂ - r₂ / ((n : ℝ) + 2))) (fun i k => DiskAdm i k) (fun _ k => diskT k)
    (d := fun o u v => ENNReal.ofReal (extendDist (ball c₂ r₂ ×ˢ ball c₂ r₂) (M o) u v))
    (F := fun i o u v =>
      ENNReal.ofReal (Real.exp (-ξ * o (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)))) *
        ENNReal.ofReal (extendDist (diskV i ×ˢ diskV i) (MV i (obsRestrict (diskV_subset i) o)) u v))
    (fun x y => measurable_ofReal_extendDist _ hMm x y)
    (fun i u v => (Real.measurable_exp.comp ((measurable_pi_apply _).const_mul _)).ennreal_ofReal.mul
      (measurable_ofReal_extendDist _ ((hMV i).comp (measurable_obsRestrict _)) u v))
  -- step 6: the rooted observation lies in `A` for almost every root
  obtain ⟨μ, hμ⟩ := hME Ω P hC hcirc hGFF hγ0 hγ2 hα
  have hA2 := ae_root_ae_rootedObs_mem_of_ae_obs_mem hI1 hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ hr₁ hr₂ hsub h0 _
    hAmeas hmem
  filter_upwards [hA2, ae_restrict_mem measurableSet_ball] with z hzA hzU
  have hzD : z ∈ ball c₂ r₂ := ball_subset_closedBall.trans hsub hzU
  have hz0 : z ≠ 0 := fun h => h0 (h ▸ ball_subset_closedBall hzD)
  -- step 7: local agreement near every point away from the root
  have h26 := ae_exists_ball_eq_mul_internalMetric_of_ae_mem_eventLocalAgreement hγ0 hγ2 h𝔇 hPhi hCM
    isOpen_ball (ball_subset_closedBall.trans hDU) (fun h => h0 (ball_subset_closedBall h)) M hρ h1 ρV MV hρV
    h1V hMV hidV Ω P hC hcirc hGFF z (hzA.mono fun ω h => h.2)
  have hlenω := hlen γ ξ 𝔇 hγ0 hγ2 h𝔇 Ω P hC hcirc hGFF
  have hWω := hins γ ξ α z hγ0 hγ2 hα hz0 Ω P hC hcirc hGFF 𝔇 h𝔇
  filter_upwards [hzA, h26, hlenω, hWω] with ω hAω h26ω hdω hWω'
  refine ⟨Real.exp (-ξ * (fieldPairing α (hC ω) ρ - γ * ∫ w, Real.log ‖w - z‖ * ρ w)), Real.exp_pos _, ?_⟩
  have hKD : ∀ n : ℕ, closedBall c₂ (r₂ - r₂ / ((n : ℝ) + 2)) ⊆ ball c₂ r₂ := fun n =>
    closedBall_subset_ball (by have : 0 < r₂ / ((n : ℝ) + 2) := by positivity
                               linarith)
  have hb := eq_rootedInternal_of_mem_eventA hdω ξ α γ hDU h0 hzD hWω'
    (fun n => isCompact_closedBall _ _) hKD hAω
    (continuousOn_ofReal_extendDist _ subset_rfl) ENNReal.ofReal_ne_top
    (fun q hq hqz => by
      obtain ⟨s, hs, -, hrest⟩ := h26ω q hq hqz
      exact ⟨s, hs, hrest⟩)
  rintro ⟨⟨u, v⟩, huv⟩
  have := hb u huv.1 v huv.2
  rwa [extendDist_of_mem _ huv] at this

end RootedLocalCover

end HarmonicBalls
