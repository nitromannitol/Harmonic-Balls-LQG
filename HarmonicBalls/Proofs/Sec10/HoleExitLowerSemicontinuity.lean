import HarmonicBalls.Proofs.Sec10.HolePointExitTime
import Mathlib.Topology.Semicontinuity.Basic

/-! # Spatial lower semicontinuity of hole exit times

The supremum of a point's positive hole times is lower semicontinuous in the
point when the closed sets have bounded hole times. No existence of holes is
asserted. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- The supremum of the positive times at which `x` is in a bounded
complementary component. It is zero when there are no such times. -/
noncomputable def holeExitTime (F : ℝ → Set ℂ) (x : ℂ) : ℝ :=
  sSup {t : ℝ | 0 < t ∧ x ∈ (F t)ᶜ ∧
    Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)}

/-- For closed sets, bounded positive hole times give a nonnegative lower
semicontinuous exit-time function. No monotonicity in time is needed. -/
theorem lowerSemicontinuous_holeExitTime
    (F : ℝ → Set ℂ) (hclosed : ∀ t, 0 < t → IsClosed (F t))
    (hbdd : ∀ x : ℂ, BddAbove {t : ℝ | 0 < t ∧ x ∈ (F t)ᶜ ∧
      Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)}) :
    LowerSemicontinuous (holeExitTime F) := by
  have hnonneg : ∀ x, 0 ≤ holeExitTime F x := by
    intro x
    by_cases h : {t : ℝ | 0 < t ∧ x ∈ (F t)ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)}.Nonempty
    · obtain ⟨s, hs⟩ := h
      exact hs.1.le.trans (le_csSup (hbdd x) hs)
    · have heq : {t : ℝ | 0 < t ∧ x ∈ (F t)ᶜ ∧
          Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)} = ∅ :=
        not_nonempty_iff_eq_empty.mp h
      unfold holeExitTime
      rw [heq]
      simp
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro a
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  change a < holeExitTime F x at hx
  by_cases ha : a < 0
  · exact Filter.Eventually.of_forall (fun y => ha.trans_le (hnonneg y))
  · have hne : {t : ℝ | 0 < t ∧ x ∈ (F t)ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)}.Nonempty := by
      by_contra h
      have heq : {t : ℝ | 0 < t ∧ x ∈ (F t)ᶜ ∧
          Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)} = ∅ :=
        not_nonempty_iff_eq_empty.mp h
      have : holeExitTime F x = 0 := by
        unfold holeExitTime
        rw [heq]
        simp
      linarith
    obtain ⟨s, hs, has⟩ := exists_lt_of_lt_csSup hne hx
    have hopen : IsOpen (connectedComponentIn (F s)ᶜ x) :=
      (hclosed s hs.1).isOpen_compl.connectedComponentIn
    have hxin : x ∈ connectedComponentIn (F s)ᶜ x := mem_connectedComponentIn hs.2.1
    apply Filter.Eventually.mono (hopen.mem_nhds hxin)
    intro y hy
    have hyout : y ∈ (F s)ᶜ := connectedComponentIn_subset _ _ hy
    have hyeq : connectedComponentIn (F s)ᶜ y = connectedComponentIn (F s)ᶜ x :=
      (connectedComponentIn_eq hy).symm
    have hys : s ∈ {t : ℝ | 0 < t ∧ y ∈ (F t)ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (F t)ᶜ y)} :=
      ⟨hs.1, hyout, hyeq ▸ hs.2.2⟩
    exact has.trans_le (le_csSup (hbdd y) hys)

universe u

/-- Under I2, each pole's hole-exit time is spatially lower semicontinuous,
simultaneously for all poles in the unit disc. -/
theorem ae_lowerSemicontinuous_clusterHoleExitTime
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      LowerSemicontinuous (holeExitTime (fun t => closure (cluster (μ ω) 1 z t))) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_times_bddAbove_ordConnected hI2
    γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω htimes
  intro z hz
  exact lowerSemicontinuous_holeExitTime _ (fun _ _ => isClosed_closure)
    (fun x => (htimes z hz x).2)

/-- Under the interior continuity assumptions, the supremum is the frontier
exit time of every point already in a bounded hole. -/
theorem ae_cluster_holeExitTime_on_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h611 : VeryGoodAnnulusHarnackTypeStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1, ∀ x : ℂ,
      x ∈ (closure (cluster (μ ω) 1 z t))ᶜ →
      Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z t))ᶜ x) →
      let L := holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x
      t < L ∧
      (∀ s : ℝ, t ≤ s → s < L →
        x ∈ (closure (cluster (μ ω) 1 z s))ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z s))ᶜ x)) ∧
      x ∈ frontier (cluster (μ ω) 1 z L) ∧
      (∀ s : ℝ, L ≤ s → x ∈ closure (cluster (μ ω) 1 z s)) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_point_exit_on_frontier hI2 hvolume h61 h611 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_hole_times_bddAbove_ordConnected hI2
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hexit htimes
  intro t ht z hz x hx hb
  obtain ⟨L, htL, hbefore, hfront, hafter⟩ := hexit t ht z hz x hx hb
  let S : Set ℝ := {s | 0 < s ∧ x ∈ (closure (cluster (μ ω) 1 z s))ᶜ ∧
    Bornology.IsBounded (connectedComponentIn (closure (cluster (μ ω) 1 z s))ᶜ x)}
  have htS : t ∈ S := ⟨ht, hx, hb⟩
  have hSbd : BddAbove S := (htimes z hz x).2
  have hsupL : sSup S ≤ L := by
    apply csSup_le ⟨t, htS⟩
    intro s hs
    by_contra h
    have hLs : L ≤ s := (lt_of_not_ge h).le
    exact hs.2.1 (hafter s hLs)
  have hLsup : L ≤ sSup S := by
    by_contra h
    have hsupL' : sSup S < L := lt_of_not_ge h
    let s := (max t (sSup S) + L) / 2
    have hmax : max t (sSup S) < L := max_lt htL hsupL'
    have hts : t ≤ s := by dsimp [s]; linarith [le_max_left t (sSup S)]
    have hsL : s < L := by dsimp [s]; linarith
    have hsupS : sSup S < s := by dsimp [s]; linarith [le_max_right t (sSup S)]
    have hs : s ∈ S := ⟨ht.trans_le hts, hbefore s hts hsL⟩
    exact (not_lt_of_ge (le_csSup hSbd hs)) hsupS
  have heq : holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x = L :=
    le_antisymm hsupL hLsup
  simpa only [heq] using And.intro htL (And.intro hbefore (And.intro hfront hafter))

end HarmonicBalls
