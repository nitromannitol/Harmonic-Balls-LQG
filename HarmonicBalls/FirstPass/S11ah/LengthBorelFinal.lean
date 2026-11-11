import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthChainReverse
import HarmonicBalls.FirstPass.S11ah.LengthForwardChain

/-!
# The length clause of `IsLengthMetricOn B (decoderOn B d)` is Borel

For `B = ball c r`
and a dense sequence `q` of `B`:

  `IsLengthMetricOn B (decoderOn B d) ↔ (d ∈ clausesSet B ∧ d ∈ codeSet c r) ∧ d ∈ lengthCodeSet c r q`.

Hence `{d | IsLengthMetricOn B (decoderOn B d)}` is Borel (`measurableSet_isLengthMetricOn_decoderOn`),
without any named hypothesis (the set `internalSet B` of the earlier route is not needed).
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section

namespace HarmonicBalls.FirstPassS11ahLengthBorelFinal

open HarmonicBalls.FirstPassS11ahLengthBorelClauses FirstPassS11ah HarmonicBalls
  HarmonicBalls.FirstPassS11ahLengthChainCode HarmonicBalls.FirstPassS11ahLengthChainReverse
  HarmonicBalls.FirstPassS11ahFineChainPath HarmonicBalls.FirstPassS11ahLengthForwardLocal
  HarmonicBalls.FirstPassS11ahLengthForwardChain

lemma ball_mono_expK (c : ℂ) (r : ℝ) {i j : ℕ} (h : i ≤ j) :
    ball c (r - 1 / ((i : ℝ) + 2)) ⊆ ball c (r - 1 / ((j : ℝ) + 2)) := by
  apply Metric.ball_subset_ball
  have hle : (i : ℝ) ≤ j := Nat.cast_le.2 h
  have : 1 / ((j : ℝ) + 2) ≤ 1 / ((i : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- A compact subset of `ball c r` lies in some level `expK c r j`. -/
lemma compact_sub_expK {c : ℂ} {r : ℝ} {s : Set ℂ} (hs : IsCompact s) (hsB : s ⊆ ball c r) :
    ∃ j : ℕ, s ⊆ expK c r j := by
  have hdir : Directed (· ⊆ ·) (fun j : ℕ => ball c (r - 1 / ((j : ℝ) + 2))) := by
    intro i j
    exact ⟨max i j, ball_mono_expK c r (le_max_left i j), ball_mono_expK c r (le_max_right i j)⟩
  have hcov : s ⊆ ⋃ j : ℕ, ball c (r - 1 / ((j : ℝ) + 2)) := by
    intro z hz
    obtain ⟨i0, hi0⟩ := exists_eventually_mem_inner (hsB hz)
    exact mem_iUnion.2 ⟨i0, hi0 i0 le_rfl⟩
  obtain ⟨j, hj⟩ := hs.elim_directed_cover (fun j : ℕ => ball c (r - 1 / ((j : ℝ) + 2)))
    (fun j => isOpen_ball) hcov hdir
  exact ⟨j, hj.trans (ball_sub_expK' c r j)⟩

/-- The decoder of a symmetric family on `B` is globally symmetric (it vanishes off `B × B`). -/
lemma decoderOn_symm_global {B : Set ℂ} {d : C(Win B, ℝ)}
    (hsymm : ∀ z ∈ B, ∀ w ∈ B, decoderOn B d z w = decoderOn B d w z) :
    ∀ x y : ℂ, decoderOn B d x y = decoderOn B d y x := by
  intro x y
  by_cases hx : x ∈ B ∧ y ∈ B
  · exact hsymm x hx.1 y hx.2
  · have h1 : ¬ ((x, y) ∈ B ×ˢ B) := fun h => hx (Set.mem_prod.1 h)
    have h2 : ¬ ((y, x) ∈ B ×ˢ B) := fun h => hx ⟨(Set.mem_prod.1 h).2, (Set.mem_prod.1 h).1⟩
    unfold decoderOn
    simp [h1, h2]

/-- **Forward implication** (ruling 236, section 6): the length property gives the fine chains. -/
theorem lengthCodeSet_of_isLengthMetricOn {c : ℂ} {r : ℝ} {q : ℕ → ↥(ball c r)}
    {d : C(Win (ball c r), ℝ)} (hq : DenseRange q)
    (hD : IsLengthMetricOn (ball c r) (decoderOn (ball c r) d)) :
    d ∈ lengthCodeSet c r q := by
  have hgs := decoderOn_symm_global (B := ball c r) (d := d)
    (fun z hz w hw => hD.symm z hz w hw)
  show ∀ i k : ℕ, ∃ j : ℕ, i ≤ j ∧ ∀ n a b : ℕ,
    (q a : ℂ) ∈ expK c r i → (q b : ℂ) ∈ expK c r i → GoodChain c r q d j k n a b
  intro i k
  obtain ⟨K', hK'c, hK'B, hK'⟩ := uniform_near_geodesics isOpen_ball hD hgs
    (isCompact_expK c r i) (expK_subset c r i) (ρ := 1 / ((k : ℝ) + 1) / 14) (by positivity)
  obtain ⟨δ0, hδ0, hK''⟩ := hK'c.exists_cthickening_subset_open isOpen_ball hK'B
  have hKc2 : IsCompact (cthickening δ0 K') := hK'c.cthickening
  obtain ⟨j, hj⟩ := compact_sub_expK hKc2 hK''
  refine ⟨max i j, le_max_left i j, fun n a b ha hb => ?_⟩
  obtain ⟨P, hPK, hPL⟩ := hK' (q a : ℂ) ha (q b : ℂ) hb
  have hPL' : pathLength (decoderOn (ball c r) d) P ≤
      ENNReal.ofReal (decoderOn (ball c r) d (q a) (q b) + 1 / ((k : ℝ) + 1) / 2) := by
    refine le_trans hPL (ENNReal.ofReal_le_ofReal ?_)
    linarith
  refine goodChain_of_path hq hD hgs hK'B hδ0
    (fun z hz z' hz' => expK_mono' c r (le_max_right i j)
      (hj (mem_cthickening_of_dist_le z' z δ0 K' hz hz'))) P hPK hPL'

/-- **The length property is the chain code** (ruling 236, section 7). -/
theorem isLengthMetricOn_iff_chainCode {c : ℂ} {r : ℝ} {q : ℕ → ↥(ball c r)} (hq : DenseRange q)
    (d : C(Win (ball c r), ℝ)) :
    IsLengthMetricOn (ball c r) (decoderOn (ball c r) d) ↔
      (d ∈ clausesSet (ball c r) ∧ d ∈ codeSet c r) ∧ d ∈ lengthCodeSet c r q := by
  constructor
  · intro hD
    have hcl : d ∈ clausesSet (ball c r) :=
      ⟨hD.self_eq_zero, fun z hz w hw => hD.symm z hz w hw,
        fun x hx y hy z hz => hD.triangle x hx y hy z hz⟩
    have hcode : d ∈ codeSet c r :=
      (mem_codeSet_iff c r d).2 (codeSet_of_V2 hD.continuousOn hD.self_eq_zero
        (fun x hx y hy z hz => hD.triangle x hx y hy z hz) (V2_of_isLengthMetricOn isOpen_ball hD))
    exact ⟨⟨hcl, hcode⟩, lengthCodeSet_of_isLengthMetricOn hq hD⟩
  · rintro ⟨⟨hcl, hcode⟩, hlen⟩
    exact isLengthMetricOn_of_chainCode hq hcl hcode hlen

/-- **Final Borel theorem** (ruling 236, section 7): the set of decoders whose length clause holds on
`ball c r` is Borel. No named hypothesis is used. -/
theorem measurableSet_isLengthMetricOn_decoderOn {c : ℂ} {r : ℝ} (hr : 0 < r) :
    MeasurableSet {d : C(Win (ball c r), ℝ) |
      IsLengthMetricOn (ball c r) (decoderOn (ball c r) d)} := by
  have : Nonempty ↥(ball c r) := ⟨⟨c, mem_ball_self hr⟩⟩
  have hq := TopologicalSpace.denseRange_denseSeq ↥(ball c r)
  have hEq : {d : C(Win (ball c r), ℝ) | IsLengthMetricOn (ball c r) (decoderOn (ball c r) d)} =
      (clausesSet (ball c r) ∩ codeSet c r) ∩
        lengthCodeSet c r (TopologicalSpace.denseSeq ↥(ball c r)) := by
    ext d
    exact isLengthMetricOn_iff_chainCode hq d
  rw [hEq]
  exact ((measurableSet_clausesSet (ball c r)).inter (measurableSet_codeSet c r)).inter
    (measurableSet_lengthCodeSet c r _)

end HarmonicBalls.FirstPassS11ahLengthBorelFinal
