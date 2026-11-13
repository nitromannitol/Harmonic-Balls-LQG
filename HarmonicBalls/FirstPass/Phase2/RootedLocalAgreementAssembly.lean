import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementNear
import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementCover

/-!
# Local agreement near every point away from the root, from the local-agreement event

Let `D ⊆ ℂ` be open, `M o` a continuous function on `D × D` and, for each rational disk `V i` with closure in `D`,
`M_V i o` a continuous function on `V i × V i` and a scalar `c₁ i o < ∞`. Suppose `o` lies in the local-agreement event
of `Phase2/RootedLocalAgreementEvent.lean` for the rational cover of `Phase2/RootedLocalAgreementCover.lean`, with the
distance `ofReal (M o)` and the local functions `c₁ i o · ofReal (M_V i o)`. Suppose further that for every disk `V i`
with a rational margin `R` avoiding the root `z` there is `c₂` with `c₁ i o · c₂ = b`, the rooted identity
`ofReal (M_V i o) = c₂ · D(·,·; V i)` holds on `V i × V i`, and the internal metrics `D(·,·; D)` and `D(·,·; V i)` agree
near every point of `V i`. Then near every point `q ≠ z` of `D`, `ofReal (M o) = b · D(·,·; D)`
(`exists_ball_eq_mul_internalMetric_of_mem_eventLocalAgreement`). This is the deterministic part of the local
agreement near every point away from the insertion.

Terminology: internal metric `D(·,·; U)` (Armstrong-Kuusi-Mourrat); rooted (quantum-typical) point (Duplantier-Sheffield).
-/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal

namespace RootedLocalCover

/-- The rational disks of the cover are connected. -/
theorem isConnected_diskV {D : Set ℂ} (i : DiskIndex D) : IsConnected (diskV i) :=
  ⟨nonempty_ball.2 i.2.1, (convex_ball _ _).isPreconnected⟩

/-- **Local agreement near every point away from the root.** If `o` lies in the local-agreement event of the
rational cover of `D`, with distance `ofReal (M o)` and local functions `c₁ i o · ofReal (M_V i o)`, and for every disk
`V i` with a rational margin avoiding `z` there is a scalar `c₂` with `c₁ i o · c₂ = b`, the rooted identity on
`V i × V i` and the agreement of the internal metrics of `D` and `V i` near the points of `V i`, then
`ofReal (M o) = b · internalMetric e D` on a ball around every `q ∈ D`, `q ≠ z`. -/
theorem exists_ball_eq_mul_internalMetric_of_mem_eventLocalAgreement {Ω : Type*} {D : Set ℂ} (hD : IsOpen D)
    {z : ℂ} (M : Ω → C(↥(D ×ˢ D), ℝ)) (MV : (i : DiskIndex D) → Ω → C(↥(diskV i ×ˢ diskV i), ℝ))
    (c₁ : DiskIndex D → Ω → ℝ≥0∞) {o : Ω}
    (ho : o ∈ eventLocalAgreement (ratPts D) (fun i k => DiskAdm i k) (fun _ k => diskT k)
      (fun o u v => ENNReal.ofReal (extendDist (D ×ˢ D) (M o) u v))
      (fun i o u v => c₁ i o * ENNReal.ofReal (extendDist (diskV i ×ˢ diskV i) (MV i o) u v)))
    (hc₁ : ∀ i, c₁ i o ≠ ⊤) {e : ℂ → ℂ → ℝ} {b : ℝ≥0∞}
    (hloc : ∀ i : DiskIndex D, ∀ R : ℚ, rad i.1 < R → closedBall (cen i.1) R ⊆ D →
      z ∉ closedBall (cen i.1) R → ∃ c₂ : ℝ≥0∞, c₁ i o * c₂ = b ∧
        (∀ p : ↥(diskV i ×ˢ diskV i),
          ENNReal.ofReal (MV i o p) = c₂ * internalMetric e (diskV i) p.1.1 p.1.2) ∧
        ∀ q ∈ diskV i, ∃ s > 0, ∀ u ∈ ball q s, ∀ v ∈ ball q s,
          internalMetric e D u v = internalMetric e (diskV i) u v) :
    ∀ q ∈ D, q ≠ z → ∃ s > 0, ball q s ⊆ D ∧ ∀ u ∈ ball q s, ∀ v ∈ ball q s,
      ENNReal.ofReal (extendDist (D ×ˢ D) (M o) u v) = b * internalMetric e D u v := by
  intro q hq hqz
  obtain ⟨i, R, hR, hRD, hzR, k, hk, hqk⟩ := exists_diskIndex_of_ne hD hq hqz
  obtain ⟨c₂, hb, hroot, hL3⟩ := hloc i R hR hRD hzR
  obtain ⟨η, hη, hA3⟩ := ho i k hk
  have hqV : q ∈ diskV i := diskT_subset_diskV hk (interior_subset hqk)
  obtain ⟨s, hs, hsD, h⟩ := exists_ball_eq_mul_internalMetric_of_decoders (diskV_subset i)
    (diskT_subset_diskV hk) ((diskV_subset i).trans (subset_closure_ratPts hD)) (M o) (MV i o) (hc₁ i)
    (η := (η : ℝ)) (by exact_mod_cast hη) (fun u hu v hv huT hvT huv => hA3 u hu v hv huT hvT huv) hroot hqk
    (hL3 q hqV)
  exact ⟨s, hs, hsD, fun u hu v hv => by rw [h u hu v hv, hb]⟩

end RootedLocalCover

end HarmonicBalls
