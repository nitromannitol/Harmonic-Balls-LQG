import Mathlib

/-!
# The rational cover of a planar domain used by the local-agreement event

Let `D ⊆ ℂ` be open. The local-agreement event of `Phase2/RootedLocalAgreementEvent.lean` is indexed by
* the rational disks `V i = ball (cen i) (rad i)` whose closures lie in `D` (index type `DiskIndex D`, countable);
* for each such disk, the rational closed disks `T k = closedBall (cen k) (rad k)` of positive radius inside `V i`
  (admissibility `DiskAdm i k`);
and it is evaluated at the points of `D` with rational coordinates (`ratPts D`, countable and dense in `D`).

This module proves the deterministic facts about these data:
* `isOpen_diskV`, `diskV_subset`, `isCompact_diskT`, `diskT_subset_diskV`: the hypotheses on `V` and `T`;
* `countable_ratPts`, `ratPts_subset`, `subset_closure_ratPts`: `ratPts D` is a countable dense subset of `D`;
* `exists_diskIndex_of_ne`: for `q ∈ D` and `z ≠ q` there are a disk `V i ∋ q`, a rational margin `R > rad i` with
  `closedBall (cen i) R ⊆ D` and `z ∉ closedBall (cen i) R`, and an admissible `k` with `q` in the interior of `T k`.
-/

namespace HarmonicBalls

open Set Metric Topology

namespace RootedLocalCover

/-- The complex number `p.1 + p.2.1 · i` with rational coordinates. -/
noncomputable def cen (p : ℚ × ℚ × ℚ) : ℂ := ⟨(p.1 : ℝ), (p.2.1 : ℝ)⟩

/-- The rational radius `p.2.2`. -/
def rad (p : ℚ × ℚ × ℚ) : ℝ := (p.2.2 : ℝ)

/-- A rational disk of positive radius whose closure lies in `D`. -/
def ValidDisk (D : Set ℂ) (v : ℚ × ℚ × ℚ) : Prop :=
  0 < rad v ∧ closedBall (cen v) (rad v) ⊆ D

/-- The index type of the rational disks with closure in `D`. -/
abbrev DiskIndex (D : Set ℂ) : Type := {v : ℚ × ℚ × ℚ // ValidDisk D v}

/-- The open disk of an index. -/
def diskV {D : Set ℂ} (i : DiskIndex D) : Set ℂ := ball (cen i.1) (rad i.1)

/-- The closed rational disk of `k`. -/
def diskT (k : ℚ × ℚ × ℚ) : Set ℂ := closedBall (cen k) (rad k)

/-- Admissibility: `T k` has positive radius and lies in `V i`. -/
def DiskAdm {D : Set ℂ} (i : DiskIndex D) (k : ℚ × ℚ × ℚ) : Prop :=
  0 < rad k ∧ diskT k ⊆ diskV i

/-- The points of `D` with rational coordinates. -/
def ratPts (D : Set ℂ) : Set ℂ := D ∩ range (fun p : ℚ × ℚ => (⟨(p.1 : ℝ), (p.2 : ℝ)⟩ : ℂ))

theorem isOpen_diskV {D : Set ℂ} (i : DiskIndex D) : IsOpen (diskV i) := isOpen_ball

theorem diskV_subset {D : Set ℂ} (i : DiskIndex D) : diskV i ⊆ D :=
  ball_subset_closedBall.trans i.2.2

theorem isCompact_diskT (k : ℚ × ℚ × ℚ) : IsCompact (diskT k) := isCompact_closedBall _ _

theorem diskT_subset_diskV {D : Set ℂ} {i : DiskIndex D} {k : ℚ × ℚ × ℚ} (h : DiskAdm i k) :
    diskT k ⊆ diskV i := h.2

/-- The hypothesis on the sets `T` of the local-agreement lemmas: compact and inside `V i` when admissible. -/
theorem diskT_compact_subset {D : Set ℂ} (i : DiskIndex D) (k : ℚ × ℚ × ℚ) (h : DiskAdm i k) :
    IsCompact (diskT k) ∧ diskT k ⊆ diskV i :=
  ⟨isCompact_diskT k, h.2⟩

theorem countable_ratPts (D : Set ℂ) : (ratPts D).Countable :=
  (countable_range _).mono inter_subset_right

theorem ratPts_subset (D : Set ℂ) : ratPts D ⊆ D := inter_subset_left

/-- The points with rational coordinates are dense in `ℂ`. -/
theorem denseRange_ratPt : DenseRange (fun p : ℚ × ℚ => (⟨(p.1 : ℝ), (p.2 : ℝ)⟩ : ℂ)) := by
  have h : (fun p : ℚ × ℚ => (⟨(p.1 : ℝ), (p.2 : ℝ)⟩ : ℂ)) =
      Complex.equivRealProdCLM.symm ∘ Prod.map (fun x : ℚ => (x : ℝ)) (fun x : ℚ => (x : ℝ)) := by
    funext p
    apply Complex.ext <;> simp
  rw [h]
  exact Complex.equivRealProdCLM.symm.surjective.denseRange.comp
    (Rat.denseRange_cast.prodMap Rat.denseRange_cast) Complex.equivRealProdCLM.symm.continuous

/-- `ratPts D` is dense in the open set `D`. -/
theorem subset_closure_ratPts {D : Set ℂ} (hD : IsOpen D) : D ⊆ closure (ratPts D) :=
  denseRange_ratPt.open_subset_closure_inter hD

/-- **Choice of the disk around a point away from the root.** For `D` open, `q ∈ D` and `z ≠ q` there are a rational
disk `V i` with closure in `D`, a rational margin `R > rad i` with `closedBall (cen i) R ⊆ D` and
`z ∉ closedBall (cen i) R`, and an admissible rational closed disk `T k ⊆ V i` with `q` in its interior. -/
theorem exists_diskIndex_of_ne {D : Set ℂ} (hD : IsOpen D) {q z : ℂ} (hq : q ∈ D) (hqz : q ≠ z) :
    ∃ i : DiskIndex D, ∃ R : ℚ, rad i.1 < R ∧ closedBall (cen i.1) R ⊆ D ∧ z ∉ closedBall (cen i.1) R ∧
      ∃ k : ℚ × ℚ × ℚ, DiskAdm i k ∧ q ∈ interior (diskT k) := by
  obtain ⟨r, hr, hrD⟩ := Metric.isOpen_iff.1 hD q hq
  set ρ : ℝ := min r (dist q z) with hρ
  have hqz' : 0 < dist q z := dist_pos.2 hqz
  have hρ0 : 0 < ρ := lt_min hr hqz'
  have hρr : ρ ≤ r := min_le_left _ _
  have hρz : ρ ≤ dist q z := min_le_right _ _
  obtain ⟨⟨a, b⟩, hab⟩ := denseRange_ratPt.exists_mem_open (isOpen_ball (x := q) (ε := ρ / 8))
    (nonempty_ball.2 (show 0 < ρ / 8 by positivity))
  rw [mem_ball] at hab
  set c : ℂ := ⟨(a : ℝ), (b : ℝ)⟩ with hc
  have hcq : dist c q < ρ / 8 := hab
  obtain ⟨t', ht'1, ht'2⟩ := exists_rat_btwn (show ρ / 8 < ρ / 4 by linarith)
  obtain ⟨t, ht1, ht2⟩ := exists_rat_btwn (show ρ / 4 < ρ / 2 by linarith)
  obtain ⟨R, hR1, hR2⟩ := exists_rat_btwn (show ρ / 2 < 3 * ρ / 4 by linarith)
  have hcen : ∀ s : ℚ, cen (a, b, s) = c := fun s => rfl
  have hrad : ∀ s : ℚ, rad (a, b, s) = (s : ℝ) := fun s => rfl
  have hRD : closedBall c R ⊆ D := by
    intro w hw
    apply hrD
    rw [mem_ball]
    rw [mem_closedBall] at hw
    calc dist w q ≤ dist w c + dist c q := dist_triangle _ _ _
      _ < r := by linarith
  have hvalid : ValidDisk D (a, b, t) := by
    refine ⟨by rw [hrad]; linarith, ?_⟩
    rw [hcen, hrad]
    exact (closedBall_subset_closedBall (by linarith)).trans hRD
  refine ⟨⟨(a, b, t), hvalid⟩, R, ?_, ?_, ?_, (a, b, t'), ⟨?_, ?_⟩, ?_⟩
  · show rad (a, b, t) < R
    rw [hrad]; linarith
  · show closedBall (cen (a, b, t)) R ⊆ D
    rw [hcen]; exact hRD
  · show z ∉ closedBall (cen (a, b, t)) R
    rw [hcen, mem_closedBall, not_le]
    have h1 := dist_triangle q c z
    have h2 : dist q c = dist c q := dist_comm _ _
    have h3 : dist z c = dist c z := dist_comm _ _
    rw [h3]
    linarith
  · rw [hrad]; linarith
  · show closedBall (cen (a, b, t')) (rad (a, b, t')) ⊆ ball (cen (a, b, t)) (rad (a, b, t))
    rw [hcen, hcen, hrad, hrad]
    exact closedBall_subset_ball (by linarith)
  · show q ∈ interior (closedBall (cen (a, b, t')) (rad (a, b, t')))
    rw [hcen, hrad]
    apply interior_mono ball_subset_closedBall
    rw [isOpen_ball.interior_eq, mem_ball, dist_comm]
    linarith

end RootedLocalCover

end HarmonicBalls
