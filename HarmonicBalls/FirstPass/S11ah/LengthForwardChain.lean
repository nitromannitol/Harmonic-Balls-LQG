import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthChainCode
import HarmonicBalls.FirstPass.S11ah.LengthForwardLocal

/-!
# Discretising a path into a fine chain (B1, forward implication, owner n3)

Ruling chat 236, section 6 (forward implication, last step). A path `P` from `q a` to `q b` inside a
compact `K' ⊆ ball c r` with decoder length `≤ D(q a, q b) + η/2` is cut into `N0` pieces of parameter
length `1/N0`. The decoder increments over the pieces are `≤ 1/(n+1)` (uniform continuity of
`(s, t) ↦ D(P s, P t)` on `[0,1]²`, which vanishes on the diagonal) and their sum is `≤ D(q a, q b) + η/2`.
The interior cut points are replaced by `q`-points within a small radius, keeping the mesh and adding at most
`η/2` to the sum. The result is a `GoodChain` with vertices in `expK c r j`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section

namespace HarmonicBalls.FirstPassS11ahLengthForwardChain

open HarmonicBalls.FirstPassS11ahLengthBorelClauses FirstPassS11ah HarmonicBalls
  HarmonicBalls.FirstPassS11ahLengthChainCode HarmonicBalls.FirstPassS11ahLengthForwardLocal

/-- A finite family of positive numbers has a uniform positive lower bound on its first `N` terms. -/
lemma exists_uniform_pos (f : ℕ → ℝ) (hf : ∀ m, 0 < f m) (N : ℕ) :
    ∃ ε > 0, ∀ m < N, ε ≤ f m := by
  induction N with
  | zero => exact ⟨1, one_pos, fun m hm => absurd hm (Nat.not_lt_zero _)⟩
  | succ N ih =>
    obtain ⟨ε, hε, h⟩ := ih
    refine ⟨min ε (f N), lt_min hε (hf N), fun m hm => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hm with h1 | h1
    · exact le_trans (min_le_left _ _) (h m h1)
    · subst h1
      exact min_le_right _ _

/-- Density of `q` near a point of the ball. -/
lemma exists_q_near {c : ℂ} {r : ℝ} {q : ℕ → ↥(ball c r)} (hq : DenseRange q) {z : ℂ}
    (hz : z ∈ ball c r) {ε : ℝ} (hε : 0 < ε) : ∃ i : ℕ, dist (q i : ℂ) z < ε := by
  have hopen : IsOpen ((Subtype.val : ↥(ball c r) → ℂ) ⁻¹' ball z ε) :=
    isOpen_ball.preimage continuous_subtype_val
  obtain ⟨i, hi⟩ := hq.exists_mem_open hopen ⟨⟨z, hz⟩, mem_ball_self hε⟩
  exact ⟨i, hi⟩

/-- The uniform continuity of `(s,t) ↦ D(P s, P t)` on `[0,1]²` gives a mesh bound. -/
lemma mesh_of_path {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hD : IsLengthMetricOn B D) {x y : ℂ}
    (P : Path x y) (hPB : ∀ t, P t ∈ B) {μ : ℝ} (hμ : 0 < μ) :
    ∃ δ > 0, ∀ s t : unitInterval, dist t s < δ → D (P s) (P t) < μ := by
  have hcont : Continuous (fun p : unitInterval × unitInterval => D (P p.1) (P p.2)) := by
    have hc : Continuous (fun p : unitInterval × unitInterval => (P p.1, P p.2)) :=
      (P.continuous.comp continuous_fst).prodMk (P.continuous.comp continuous_snd)
    exact hD.continuousOn.comp_continuous hc (fun p => mk_mem_prod (hPB _) (hPB _))
  have hunif := CompactSpace.uniformContinuous_of_continuous hcont
  rw [Metric.uniformContinuous_iff] at hunif
  obtain ⟨δ, hδ, hδ'⟩ := hunif μ hμ
  refine ⟨δ, hδ, fun s t hst => ?_⟩
  have h := hδ' (a := (s, t)) (b := (s, s)) (by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hst)
  have h0 : D (P s) (P s) = 0 := hD.self_eq_zero _ (hPB s)
  simp only [h0, Real.dist_eq, sub_zero] at h
  exact lt_of_le_of_lt (le_abs_self _) h

/-- Projection of the cut points `m / N0` to the unit interval. -/
def cutPt (N0 m : ℕ) : unitInterval :=
  Set.projIcc (0 : ℝ) 1 zero_le_one ((m : ℝ) / (N0 : ℝ))

lemma cutPt_val {N0 m : ℕ} (hm : m ≤ N0) (hN : 0 < N0) :
    ((cutPt N0 m : unitInterval) : ℝ) = (m : ℝ) / (N0 : ℝ) := by
  unfold cutPt
  rw [Set.projIcc_of_mem]
  have hN' : (0 : ℝ) < N0 := Nat.cast_pos.2 hN
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hN']
  exact_mod_cast hm

lemma cutPt_zero (N0 : ℕ) : cutPt N0 0 = 0 := by
  apply Subtype.ext
  simp [cutPt]

lemma cutPt_mono (N0 : ℕ) : Monotone (cutPt N0) := by
  intro m m' h
  unfold cutPt
  apply Set.monotone_projIcc
  exact div_le_div_of_nonneg_right (Nat.cast_le.2 h) (Nat.cast_nonneg _)

/-- The partition sum of a path is bounded by its length (in `ℝ≥0∞`). -/
lemma partition_sum_le_pathLength {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hD : IsLengthMetricOn B D)
    (hgs : ∀ x y, D x y = D y x) {x y : ℂ} (P : Path x y) (hPB : ∀ t, P t ∈ B) (N : ℕ)
    (s : ℕ → unitInterval) (hs : Monotone s) :
    ENNReal.ofReal (∑ m ∈ Finset.range N, D (P (s m)) (P (s (m + 1)))) ≤ pathLength D P := by
  unfold pathLength curveLength
  refine le_iSup_of_le (N, ⟨fun m : ℕ => ((s m : unitInterval) : ℝ), ?_, fun m => (s m).2⟩) ?_
  · intro m m' h
    exact Subtype.coe_le_coe.2 (hs h)
  · rw [ENNReal.ofReal_sum_of_nonneg (fun m _ => hD.nonneg (hPB _) (hPB _))]
    refine le_of_eq (Finset.sum_congr rfl fun m _ => ?_)
    simp only [Path.extend_extends' P (s (m + 1)), Path.extend_extends' P (s m)]
    rw [hgs (P (s m)) (P (s (m + 1)))]

/-- **Discretisation** (ruling 236, section 6). A path from `q a` to `q b` inside `K'`, of length at most
`D(q a, q b) + η/2`, yields a `GoodChain` at level `j` (vertices in `expK c r j`) for every mesh `1/(n+1)`. -/
theorem goodChain_of_path {c : ℂ} {r : ℝ} {q : ℕ → ↥(ball c r)} {d : C(Win (ball c r), ℝ)}
    (hq : DenseRange q) (hD : IsLengthMetricOn (ball c r) (decoderOn (ball c r) d))
    (hgs : ∀ x y, decoderOn (ball c r) d x y = decoderOn (ball c r) d y x)
    {K' : Set ℂ} (hK'B : K' ⊆ ball c r)
    {j : ℕ} {δ : ℝ} (hδ : 0 < δ) (hKj : ∀ z ∈ K', ∀ z', dist z' z ≤ δ → z' ∈ expK c r j)
    {k n a b : ℕ} (P : Path (q a : ℂ) (q b : ℂ)) (hPK : ∀ t, P t ∈ K')
    (hPL : pathLength (decoderOn (ball c r) d) P ≤
      ENNReal.ofReal (decoderOn (ball c r) d (q a) (q b) + 1 / ((k : ℝ) + 1) / 2)) :
    GoodChain c r q d j k n a b := by
  set D := decoderOn (ball c r) d with hDdef
  have hPB : ∀ t, P t ∈ ball c r := fun t => hK'B (hPK t)
  have hμ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hη : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
  obtain ⟨δu, hδu, hmesh⟩ := mesh_of_path hD P hPB (μ := 1 / ((n : ℝ) + 1) / 2) (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt hδu
  obtain ⟨N0, hN0pos, hsp⟩ : ∃ N0 : ℕ, 0 < N0 ∧ (1 : ℝ) / (N0 : ℝ) < δu :=
    ⟨M + 1, Nat.succ_pos M, by push_cast; exact hM⟩
  have hN0R : (0 : ℝ) < N0 := Nat.cast_pos.2 hN0pos
  -- cut points on the path
  have hzK : ∀ m, P (cutPt N0 m) ∈ K' := fun m => hPK _
  have hzB : ∀ m, P (cutPt N0 m) ∈ ball c r := fun m => hK'B (hzK m)
  have hz0 : P (cutPt N0 0) = q a := by rw [cutPt_zero, P.source]
  have hzN : P (cutPt N0 N0) = q b := by
    have h1 : cutPt N0 N0 = 1 := by
      apply Subtype.ext
      rw [cutPt_val le_rfl hN0pos]
      exact div_self hN0R.ne'
    rw [h1, P.target]
  -- the mesh of the cut points
  have hzmesh : ∀ m < N0, D (P (cutPt N0 m)) (P (cutPt N0 (m + 1))) < 1 / ((n : ℝ) + 1) / 2 := by
    intro m hm
    apply hmesh
    have h1 : m ≤ N0 := by omega
    have h2 : m + 1 ≤ N0 := by omega
    rw [Subtype.dist_eq, Real.dist_eq, cutPt_val h2 hN0pos, cutPt_val h1 hN0pos]
    have e : ((m + 1 : ℕ) : ℝ) / (N0 : ℝ) - (m : ℝ) / (N0 : ℝ) = 1 / (N0 : ℝ) := by
      push_cast; ring
    rw [e, abs_of_pos (by positivity)]
    exact hsp
  -- the length of the cut polygon
  have hsum_le : ∑ m ∈ Finset.range N0, D (P (cutPt N0 m)) (P (cutPt N0 (m + 1))) ≤
      D (q a) (q b) + 1 / ((k : ℝ) + 1) / 2 := by
    have h := partition_sum_le_pathLength hD hgs P hPB N0 (cutPt N0) (cutPt_mono N0)
    have h2 := h.trans hPL
    exact (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg (hD.nonneg (q a).2 (q b).2) (by positivity))).1 h2
  -- the error radius `τ`
  obtain ⟨τ, hτ, hτ1, hτ2⟩ : ∃ τ : ℝ, 0 < τ ∧ (N0 : ℝ) * τ ≤ 1 / ((k : ℝ) + 1) / 2 ∧
      τ ≤ 1 / ((n : ℝ) + 1) / 2 := by
    refine ⟨min (1 / ((k : ℝ) + 1) / 2 / N0) (1 / ((n : ℝ) + 1) / 2),
      lt_min (by positivity) (by positivity), ?_, min_le_right _ _⟩
    calc (N0 : ℝ) * min (1 / ((k : ℝ) + 1) / 2 / N0) (1 / ((n : ℝ) + 1) / 2)
        ≤ (N0 : ℝ) * (1 / ((k : ℝ) + 1) / 2 / N0) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hN0R.le
      _ = 1 / ((k : ℝ) + 1) / 2 := by field_simp
  -- continuity radii at the cut pairs
  have hcontpair : ∀ m : ℕ, ∃ ε > 0, ∀ p ∈ ball c r, ∀ p' ∈ ball c r,
      dist p (P (cutPt N0 m)) < ε → dist p' (P (cutPt N0 (m + 1))) < ε →
        |D p p' - D (P (cutPt N0 m)) (P (cutPt N0 (m + 1)))| < τ := by
    intro m
    have hc := (continuousOn_decoderOn d) (P (cutPt N0 m), P (cutPt N0 (m + 1)))
      ⟨hzB m, hzB (m + 1)⟩
    rw [Metric.continuousWithinAt_iff] at hc
    obtain ⟨ε, hε, hε'⟩ := hc τ hτ
    refine ⟨ε, hε, fun p hp p' hp' h1 h2 => ?_⟩
    have hdist : dist ((p, p') : ℂ × ℂ) (P (cutPt N0 m), P (cutPt N0 (m + 1))) < ε := by
      rw [Prod.dist_eq]
      exact max_lt h1 h2
    have := hε' (x := (p, p')) ⟨hp, hp'⟩ hdist
    simpa [Real.dist_eq] using this
  choose! ε hε hεc using hcontpair
  obtain ⟨εu, hεu, hεu'⟩ := exists_uniform_pos ε (fun m => hε m) N0
  obtain ⟨εa, hεa, hεa1, hεa2⟩ : ∃ εa : ℝ, 0 < εa ∧ εa ≤ εu ∧ εa ≤ δ :=
    ⟨min εu δ, lt_min hεu hδ, min_le_left _ _, min_le_right _ _⟩
  -- approximating the interior cut points by `q`-points
  choose! idx hidx using fun m => exists_q_near hq (hzB m) hεa
  -- the chain
  set wN : ℕ → ℕ := fun t => if t = 0 then a else if t = N0 then b else idx t with hwN
  set Q : ℕ → ℂ := fun t => (q (wN t) : ℂ) with hQ
  have hQdist : ∀ t ≤ N0, dist (Q t) (P (cutPt N0 t)) < εa := by
    intro t _
    by_cases h0 : t = 0
    · rw [h0, hz0]
      have hw : wN 0 = a := by simp [hwN]
      show dist (q (wN 0) : ℂ) (q a) < εa
      rw [hw, dist_self]
      exact hεa
    · by_cases hN : t = N0
      · rw [hN, hzN]
        have hw : wN N0 = b := by simp [hwN, hN0pos.ne']
        show dist (q (wN N0) : ℂ) (q b) < εa
        rw [hw, dist_self]
        exact hεa
      · have hw : wN t = idx t := by simp [hwN, h0, hN]
        show dist (q (wN t) : ℂ) (P (cutPt N0 t)) < εa
        rw [hw]
        exact hidx t
  have hQball : ∀ t, Q t ∈ ball c r := fun t => (q (wN t)).2
  have hQpair : ∀ t < N0, D (Q t) (Q (t + 1)) <
      D (P (cutPt N0 t)) (P (cutPt N0 (t + 1))) + τ := by
    intro t ht
    have hd1 : dist (Q t) (P (cutPt N0 t)) < ε t :=
      lt_of_lt_of_le (hQdist t (by omega)) (le_trans hεa1 (hεu' t ht))
    have hd2 : dist (Q (t + 1)) (P (cutPt N0 (t + 1))) < ε t :=
      lt_of_lt_of_le (hQdist (t + 1) (by omega)) (le_trans hεa1 (hεu' t ht))
    have h := hεc t (Q t) (hQball t) (Q (t + 1)) (hQball (t + 1)) hd1 hd2
    have h' := (abs_sub_lt_iff.1 h).1
    linarith
  have hQmesh : ∀ t < N0, D (Q t) (Q (t + 1)) ≤ 1 / ((n : ℝ) + 1) := by
    intro t ht
    have h1 := hQpair t ht
    have h2 := hzmesh t ht
    linarith [hτ2]
  have hQsum : ∑ t ∈ Finset.range N0, D (Q t) (Q (t + 1)) ≤
      D (q a) (q b) + 1 / ((k : ℝ) + 1) := by
    have h1 : ∑ t ∈ Finset.range N0, D (Q t) (Q (t + 1)) ≤
        ∑ t ∈ Finset.range N0, (D (P (cutPt N0 t)) (P (cutPt N0 (t + 1))) + τ) :=
      Finset.sum_le_sum fun t ht => le_of_lt (hQpair t (Finset.mem_range.1 ht))
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    linarith [hsum_le, hτ1]
  have hsumF : ∑ t : Fin N0, D (Q (t : ℕ)) (Q ((t : ℕ) + 1)) =
      ∑ t ∈ Finset.range N0, D (Q t) (Q (t + 1)) :=
    Fin.sum_univ_eq_sum_range (fun t => D (Q t) (Q (t + 1))) N0
  refine ⟨N0, fun t : Fin (N0 + 1) => wN (t : ℕ), ?_, ?_, ?_, ?_, ?_⟩
  · show wN ((0 : Fin (N0 + 1)) : ℕ) = a
    simp [hwN]
  · show wN ((Fin.last N0 : Fin (N0 + 1)) : ℕ) = b
    rw [Fin.val_last]
    simp [hwN, hN0pos.ne']
  · intro t
    have hmem := hQdist (t : ℕ) (Nat.lt_succ_iff.1 t.2)
    exact hKj _ (hzK _) (Q (t : ℕ)) (le_of_lt (lt_of_lt_of_le hmem hεa2))
  · intro t
    exact hQmesh t t.2
  · have key := hQsum
    rw [← hsumF] at key
    exact key

end HarmonicBalls.FirstPassS11ahLengthForwardChain
