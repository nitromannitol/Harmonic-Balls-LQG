import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementUnrootedMembership
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementCover
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementObs
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementNear
import HarmonicBalls.FirstPass.S11c.ShiftObs11_7
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity

/-!
# The unrooted observation lies almost surely in the concrete local-agreement event (step 5)

Let `D = ball c r` and let `(ρ, M)` and `(ρ_i, M_i)` be the unit-mass test functions and the decoders of the
fixed-metric identity (18) on `D` and on the rational disks `V i = diskV i ⊆ D` (`Phase2/RootedLocalAgreementUnrooted`):
almost surely `ofReal (M o) = exp(-ξ ⟨h^α, ρ⟩) · D(·,·; D)` on `D × D` for the observation `o` of `D`, and the same on
each `V i` with `ρ_i`. This module proves that the observation `o = localMeanZeroObs α D (hC ω)` of the field lies
almost surely in the concrete event `A` of the rational cover (`Phase2/RootedLocalAgreementCover`):

* `exists_closedBall_of_isCompact_subset_ball`: every compact subset of a ball lies in `closedBall c (r - r/(n+2))`;
* `mem_eventA_concrete`: deterministic membership from the two identities (step 5, deterministic part);
* `ae_localMeanZeroObs_meanZeroTestOfSub`: for a whole-plane GFF the observation of the difference `ρ - ρ_i` is
  almost surely the difference of the pairings, so the scalars of `D` and of `V i` combine (`exp(-ξ(a - b)) exp(-ξ b)`);
* `ae_localMeanZeroObs_mem_eventA`: the almost sure membership.

Terminology: internal metric (Armstrong-Kuusi-Mourrat); Euclidean length metric (Gwynne-Miller); whole-plane GFF
(Duplantier-Sheffield).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace UnrootedLocal

open RootedLocalCover

/-- Every compact subset of a ball lies in a slightly smaller closed ball of the exhaustion `n ↦ closedBall c (r - r/(n+2))`. -/
theorem exists_closedBall_of_isCompact_subset_ball {c : ℂ} {r : ℝ} {C : Set ℂ} (hC : IsCompact C)
    (hCD : C ⊆ ball c r) : ∃ n : ℕ, C ⊆ closedBall c (r - r / ((n : ℝ) + 2)) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, empty_subset _⟩
  obtain ⟨x₀, hx₀, hmax⟩ := hC.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
  have hx0 : dist x₀ c < r := mem_ball.1 (hCD hx₀)
  have hr : 0 < r - dist x₀ c := sub_pos.2 hx0
  have hr0 : 0 < r := lt_of_le_of_lt dist_nonneg hx0
  obtain ⟨n, hn⟩ := exists_nat_gt (r / (r - dist x₀ c))
  refine ⟨n, fun x hx => ?_⟩
  have h1 : dist x c ≤ dist x₀ c := hmax hx
  have hn' : r < (n : ℝ) * (r - dist x₀ c) := (div_lt_iff₀ hr).1 hn
  have h2 : r / ((n : ℝ) + 2) ≤ r - dist x₀ c := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [mem_closedBall]
  linarith

/-- **Deterministic membership in the concrete event.** If the decoded function `ofReal (M o)` on `D × D` and the local
decoded functions `c₁ i o · ofReal (M_i o)` on `V i × V i` are the same multiple `c ≠ ∞` of the internal metrics of a
Euclidean length metric `F` on `D` and on `V i`, then `o` lies in the event of the rational cover of the open
path-connected set `D`. -/
theorem mem_eventA_concrete {Ω : Type*} {D : Set ℂ} (hD : IsOpen D) (hDpc : IsPathConnected D)
    {K : ℕ → Set ℂ} (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ D → ∃ n, C ⊆ K n) {F : ℂ → ℂ → ℝ}
    (hF : IsEuclideanLengthMetric F) (M : Ω → C(↥(D ×ˢ D), ℝ))
    (MV : (i : DiskIndex D) → Ω → C(↥(diskV i ×ˢ diskV i), ℝ)) (c₁ : DiskIndex D → Ω → ℝ≥0∞) {o : Ω}
    {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hd : ∀ p : ↥(D ×ˢ D), ENNReal.ofReal (M o p) = c * internalMetric F D p.1.1 p.1.2)
    (hFam : ∀ i, ∀ p : ↥(diskV i ×ˢ diskV i),
      c₁ i o * ENNReal.ofReal (MV i o p) = c * internalMetric F (diskV i) p.1.1 p.1.2) :
    o ∈ eventA (ratPts D) K (fun i k => DiskAdm i k) (fun _ k => diskT k)
      (fun o u v => ENNReal.ofReal (extendDist (D ×ˢ D) (M o) u v))
      (fun i o u v => c₁ i o * ENNReal.ofReal (extendDist (diskV i ×ˢ diskV i) (MV i o) u v)) := by
  refine mem_eventA_of_internalMetric hF hD hDpc (ratPts_subset D) (subset_closure_ratPts hD) hK
    (fun i => diskV i) isOpen_diskV diskV_subset (fun i k hik => ⟨isCompact_diskT k, diskT_subset_diskV hik⟩)
    hc ?_ ?_
  · intro u hu v hv
    have huv : (u, v) ∈ D ×ˢ D := ⟨ratPts_subset D hu, ratPts_subset D hv⟩
    rw [extendDist_of_mem _ huv]
    exact hd ⟨(u, v), huv⟩
  · intro i u hu hui v hv hvi
    have huv : (u, v) ∈ diskV i ×ˢ diskV i := ⟨hui, hvi⟩
    rw [extendDist_of_mem _ huv]
    exact hFam i ⟨(u, v), huv⟩

/-- **The observation of a difference of normalizing test functions.** If `T` is linear on `ρ - ρ_V`, the local
mean-zero observation `⟨h^α, ρ - ρ_V⟩` is the difference of the pairings. -/
theorem localMeanZeroObs_meanZeroTestOfSub {V D : Set ℂ} (hVD : V ⊆ D) {ρ ρV : ℂ → ℝ}
    (hρ : IsTestFunction D ρ) (hρV : IsTestFunction V ρV) (h1 : ∫ x, ρ x = 1) (h1V : ∫ x, ρV x = 1) (α : ℝ)
    (T : (ℂ → ℝ) → ℝ) (hlin : T (fun x => ρ x - ρV x) = T ρ - T ρV) :
    localMeanZeroObs α D T (meanZeroTestOfSub hVD hρ hρV h1 h1V) = fieldPairing α T ρ - fieldPairing α T ρV := by
  have hρV' : IsTestFunction D ρV := hρV.mono_set hVD
  have i0 : Integrable (fun w => ρ w * Real.log ‖w‖) := by
    simpa only [sub_zero] using S11c.integrable_mul_logNorm_sub hρ 0
  have i0V : Integrable (fun w => ρV w * Real.log ‖w‖) := by
    simpa only [sub_zero] using S11c.integrable_mul_logNorm_sub hρV' 0
  have hlog : ∫ x, (ρ x - ρV x) * Real.log ‖x‖ =
      (∫ x, ρ x * Real.log ‖x‖) - ∫ x, ρV x * Real.log ‖x‖ := by
    rw [← integral_sub i0 i0V]
    congr 1
    funext x
    ring
  simp only [localMeanZeroObs, meanZeroTestOfSub_val, fieldPairing, hlin]
  rw [hlog]
  ring

/-- **Almost sure additivity for a whole-plane GFF.** The pairing of a whole-plane GFF is almost surely additive on
`ρ - ρ_V`, so almost surely the observation of `ρ - ρ_V` is the difference of the pairings with `ρ` and `ρ_V`. -/
theorem ae_localMeanZeroObs_meanZeroTestOfSub {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {V D : Set ℂ}
    (hVD : V ⊆ D) {ρ ρV : ℂ → ℝ} (hρ : IsTestFunction D ρ) (hρV : IsTestFunction V ρV) (h1 : ∫ x, ρ x = 1)
    (h1V : ∫ x, ρV x = 1) (α : ℝ) :
    ∀ᵐ ω ∂P, localMeanZeroObs α D (hC ω) (meanZeroTestOfSub hVD hρ hρV h1 h1V) =
      fieldPairing α (hC ω) ρ - fieldPairing α (hC ω) ρV := by
  filter_upwards [hh.ae_pairing_linear_combination (hρ.mono_set (subset_univ D))
    (hρV.mono_set (subset_univ V)) 1 (-1)] with ω hω
  refine localMeanZeroObs_meanZeroTestOfSub hVD hρ hρV h1 h1V α (hC ω) ?_
  have hfun : (fun x => ρ x - ρV x) = fun x => 1 * ρ x + -1 * ρV x := by
    funext x
    ring
  rw [hfun, hω]
  ring

/-- **The unrooted observation lies almost surely in the concrete event.** For a whole-plane GFF `h`, the decoders
`M` of `D` and `M_i` of the rational disks `V i ⊆ D` with the identities (18) (with the unit-mass test functions `ρ`,
`ρ_i`) almost surely, and a family `F ω` of Euclidean length metrics almost surely, the observation
`localMeanZeroObs α D (hC ω)` lies almost surely in the event `A` of the rational cover, whose local functions are
`exp(-ξ ⟨o, ρ - ρ_i⟩) · M_i (o|_{V i})`. -/
theorem ae_localMeanZeroObs_mem_eventA {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {D : Set ℂ}
    (hD : IsOpen D) (hDpc : IsPathConnected D) {K : ℕ → Set ℂ}
    (hK : ∀ C : Set ℂ, IsCompact C → C ⊆ D → ∃ n, C ⊆ K n) {F : Ω → ℂ → ℂ → ℝ}
    (hF : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (F ω)) (α ξ : ℝ) {ρ : ℂ → ℝ} (hρ : IsTestFunction D ρ)
    (h1 : ∫ x, ρ x = 1) {ρV : DiskIndex D → ℂ → ℝ} (hρV : ∀ i, IsTestFunction (diskV i) (ρV i))
    (h1V : ∀ i, ∫ x, ρV i x = 1) (M : (MeanZeroTest D → ℝ) → C(↥(D ×ˢ D), ℝ))
    (MV : (i : DiskIndex D) → (MeanZeroTest (diskV i) → ℝ) → C(↥(diskV i ×ˢ diskV i), ℝ))
    (hMD : ∀ᵐ ω ∂P, ∀ p : ↥(D ×ˢ D), ENNReal.ofReal (M (localMeanZeroObs α D (hC ω)) p) =
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing α (hC ω) ρ)) * internalMetric (F ω) D p.1.1 p.1.2)
    (hMV : ∀ i, ∀ᵐ ω ∂P, ∀ p : ↥(diskV i ×ˢ diskV i),
      ENNReal.ofReal (MV i (localMeanZeroObs α (diskV i) (hC ω)) p) =
        ENNReal.ofReal (Real.exp (-ξ * fieldPairing α (hC ω) (ρV i))) *
          internalMetric (F ω) (diskV i) p.1.1 p.1.2) :
    ∀ᵐ ω ∂P, localMeanZeroObs α D (hC ω) ∈
      eventA (ratPts D) K (fun i k => DiskAdm i k) (fun _ k => diskT k)
        (fun o u v => ENNReal.ofReal (extendDist (D ×ˢ D) (M o) u v))
        (fun i o u v => ENNReal.ofReal (Real.exp (-ξ * o (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1
            (h1V i)))) *
          ENNReal.ofReal (extendDist (diskV i ×ˢ diskV i) (MV i (obsRestrict (diskV_subset i) o)) u v)) := by
  have hall : ∀ᵐ ω ∂P, ∀ i : DiskIndex D,
      localMeanZeroObs α D (hC ω) (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)) =
        fieldPairing α (hC ω) ρ - fieldPairing α (hC ω) (ρV i) :=
    ae_all_iff.2 fun i => ae_localMeanZeroObs_meanZeroTestOfSub hh (diskV_subset i) hρ (hρV i) h1 (h1V i) α
  have hMV' := ae_all_iff.2 hMV
  filter_upwards [hF, hMD, hMV', hall] with ω hFω hMDω hMVω hallω
  refine mem_eventA_concrete hD hDpc hK hFω M (fun i o => MV i (obsRestrict (diskV_subset i) o))
    (fun i o => ENNReal.ofReal (Real.exp (-ξ * o (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)))))
    ENNReal.ofReal_ne_top hMDω ?_
  intro i p
  have hconst : ENNReal.ofReal (Real.exp (-ξ * localMeanZeroObs α D (hC ω)
        (meanZeroTestOfSub (diskV_subset i) hρ (hρV i) h1 (h1V i)))) *
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing α (hC ω) (ρV i))) =
      ENNReal.ofReal (Real.exp (-ξ * fieldPairing α (hC ω) ρ)) := by
    rw [hallω i, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have hp := hMVω i p
  rw [obsRestrict_localMeanZeroObs]
  rw [hp, ← mul_assoc, hconst]

end UnrootedLocal

end HarmonicBalls
