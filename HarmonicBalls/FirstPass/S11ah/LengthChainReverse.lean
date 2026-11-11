import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthChainCode
import HarmonicBalls.FirstPass.S11ah.FineChainPath

/-!
# The chain code gives the length clause

Let `B = ball c r`, `q` dense in `B`, and let `d` satisfy
the metric clauses on `B`, `codeSet` and `lengthCodeSet`. Then `IsLengthMetricOn B (decoderOn B d)`.

For `z, w ∈ B`: the lower bound `ofReal D(z,w) ≤ internalMetric` comes from the partition `{0,1}`. The upper
bound uses fine chains from `z` to `w`: `z` and `w` are joined to nearby `q`-points, the code gives chains
between those `q`-points, and `exists_path_of_fine_chains` turns the glued chain into a path in `expK J`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
open Fin.NatCast
noncomputable section

namespace HarmonicBalls.FirstPassS11ahLengthChainReverse

open HarmonicBalls.FirstPassS11ahLengthBorelClauses HarmonicBalls.FirstPassS11ahLengthChainCode
  HarmonicBalls.FirstPassS11ahFineChainPath FirstPassS11ah HarmonicBalls

/-! ### The exhaustion of `ball c r` -/

lemma expK_mono' (c : ℂ) (r : ℝ) {i j : ℕ} (hij : i ≤ j) : expK c r i ⊆ expK c r j := by
  intro z hz
  have hle : (i : ℝ) ≤ j := Nat.cast_le.2 hij
  have h1 : 1 / ((j : ℝ) + 2) ≤ 1 / ((i : ℝ) + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  unfold expK at hz ⊢
  rw [mem_closedBall] at hz ⊢
  linarith

lemma ball_sub_expK' (c : ℂ) (r : ℝ) (I : ℕ) : ball c (r - 1 / ((I : ℝ) + 2)) ⊆ expK c r I :=
  fun _ hz => Metric.ball_subset_closedBall hz

lemma exists_eventually_mem_inner {c : ℂ} {r : ℝ} {z : ℂ} (hz : z ∈ ball c r) :
    ∃ i0 : ℕ, ∀ I : ℕ, i0 ≤ I → z ∈ ball c (r - 1 / ((I : ℝ) + 2)) := by
  rw [mem_ball] at hz
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hz)
  refine ⟨n, fun I hI => ?_⟩
  rw [mem_ball]
  have hle : (n : ℝ) ≤ I := Nat.cast_le.2 hI
  have h1 : 1 / ((I : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  linarith

/-- Pointwise smallness of the decoder near a point of the ball (continuity at `(p, p)`). -/
lemma decoder_small_near {c : ℂ} {r : ℝ} {d : C(Win (ball c r), ℝ)}
    (hself : ∀ z ∈ ball c r, decoderOn (ball c r) d z z = 0)
    {p : ℂ} (hp : p ∈ ball c r) {e : ℝ} (he : 0 < e) :
    ∃ δ > 0, ∀ p' ∈ ball c r, dist p' p < δ → decoderOn (ball c r) d p p' < e := by
  have hc := (continuousOn_decoderOn d) (p, p) ⟨hp, hp⟩
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc e he
  refine ⟨δ, hδ, fun p' hp' hd => ?_⟩
  have hdist : dist ((p, p') : ℂ × ℂ) (p, p) < δ := by
    rw [Prod.dist_eq, dist_self, max_eq_right dist_nonneg]
    exact hd
  have h := hδ' (x := (p, p')) ⟨hp, hp'⟩ hdist
  rw [hself p hp, Real.dist_eq, sub_zero] at h
  exact lt_of_le_of_lt (le_abs_self _) h

/-- A `V2` function is separated: `D z w = 0` forces `z = w`. -/
lemma sep_of_V2 {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hV : V2 B D) :
    ∀ z ∈ B, ∀ w ∈ B, D z w = 0 → z = w := by
  intro z hz w hw h0
  by_contra hne
  have hδ : 0 < dist w z := dist_pos.2 (Ne.symm hne)
  obtain ⟨e, he, hVe⟩ := hV z hz (dist w z) hδ
  have := hVe w hw le_rfl
  linarith

/-! ### Chains as `ℕ`-indexed sequences -/

/-- A fine chain of the code, as an `ℕ`-indexed sequence of points of `expK c r j`. -/
lemma goodChain_to_nat {c : ℂ} {r : ℝ} {q : ℕ → ↥(ball c r)} {d : C(Win (ball c r), ℝ)}
    {j k n a b : ℕ} (h : GoodChain c r q d j k n a b) :
    ∃ N : ℕ, ∃ u : ℕ → ℂ, u 0 = (q a : ℂ) ∧ u N = (q b : ℂ) ∧ (∀ t ≤ N, u t ∈ expK c r j) ∧
      (∀ t < N, decoderOn (ball c r) d (u t) (u (t + 1)) ≤ 1 / ((n : ℝ) + 1)) ∧
      chainSum (decoderOn (ball c r) d) u N ≤
        decoderOn (ball c r) d (q a) (q b) + 1 / ((k : ℝ) + 1) := by
  obtain ⟨N, w, h0, hN, hvert, hmesh, hsum⟩ := h
  have hc : ∀ t : Fin N, ((t : ℕ) : Fin (N + 1)) = Fin.castSucc t := fun t => by
    ext
    simp
  have hs : ∀ t : Fin N, (((t : ℕ) + 1 : ℕ) : Fin (N + 1)) = Fin.succ t := fun t => by
    ext
    simp
  refine ⟨N, fun t => (q (w (t : Fin (N + 1))) : ℂ), ?_, ?_, ?_, ?_, ?_⟩
  · show (q (w ((0 : ℕ) : Fin (N + 1))) : ℂ) = q a
    rw [Nat.cast_zero, h0]
  · show (q (w ((N : ℕ) : Fin (N + 1))) : ℂ) = q b
    rw [Fin.natCast_eq_last, hN]
  · intro t _
    exact hvert _
  · intro t ht
    show decoderOn (ball c r) d (q (w ((t : ℕ) : Fin (N + 1))) : ℂ)
      (q (w (((t + 1 : ℕ)) : Fin (N + 1))) : ℂ) ≤ _
    have ht' : t < N := ht
    have e1 : ((t : ℕ) : Fin (N + 1)) = Fin.castSucc (⟨t, ht'⟩ : Fin N) := hc ⟨t, ht'⟩
    have e2 : (((t + 1 : ℕ)) : Fin (N + 1)) = Fin.succ (⟨t, ht'⟩ : Fin N) := hs ⟨t, ht'⟩
    rw [e1, e2]
    exact hmesh ⟨t, ht'⟩
  · unfold chainSum
    rw [← Fin.sum_univ_eq_sum_range]
    refine le_of_eq_of_le ?_ hsum
    refine Finset.sum_congr rfl fun t _ => ?_
    show decoderOn (ball c r) d (q (w ((t : ℕ) : Fin (N + 1))) : ℂ)
      (q (w (((t : ℕ) + 1 : ℕ) : Fin (N + 1))) : ℂ) = _
    rw [hc t, hs t]

/-- Glue of a chain: `z` is prepended and `w` appended to a chain `u` from `p` to `p'`. -/
def glueChain (z w : ℂ) (N : ℕ) (u : ℕ → ℂ) (t : ℕ) : ℂ :=
  if t = 0 then z else if t ≤ N + 1 then u (t - 1) else w

lemma chain_glue {D : ℂ → ℂ → ℝ} {z w p p' : ℂ} {N : ℕ} {u : ℕ → ℂ} {μ : ℝ}
    (hu0 : u 0 = p) (huN : u N = p') (hmesh : ∀ t < N, D (u t) (u (t + 1)) ≤ μ)
    (hz : D z p ≤ μ) (hw : D p' w ≤ μ) :
    ∃ v : ℕ → ℂ, v 0 = z ∧ v (N + 2) = w ∧ (∀ t ≤ N, v (t + 1) = u t) ∧
      (∀ t < N + 2, D (v t) (v (t + 1)) ≤ μ) ∧
      chainSum D v (N + 2) = D z p + chainSum D u N + D p' w := by
  have hv0 : glueChain z w N u 0 = z := by simp [glueChain]
  have hvsucc : ∀ t ≤ N, glueChain z w N u (t + 1) = u t := fun t ht => by
    simp [glueChain, ht]
  have hvN2 : glueChain z w N u (N + 2) = w := by simp [glueChain]
  have hv1 : glueChain z w N u 1 = p := by
    have := hvsucc 0 (Nat.zero_le N)
    simpa [hu0] using this
  have hvN1 : glueChain z w N u (N + 1) = p' := by
    have := hvsucc N le_rfl
    simpa [huN] using this
  refine ⟨glueChain z w N u, hv0, hvN2, hvsucc, ?_, ?_⟩
  · intro t ht
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      rw [hv0, hv1]
      exact hz
    · rcases Nat.lt_or_ge t (N + 1) with hlt | hge
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        rw [hvsucc s (by omega), hvsucc (s + 1) (by omega)]
        exact hmesh s (by omega)
      · have htN : t = N + 1 := by omega
        subst htN
        rw [hvN1, hvN2]
        exact hw
  · unfold chainSum
    rw [Finset.sum_range_succ', Finset.sum_range_succ]
    have hmid : ∑ x ∈ Finset.range N,
        D (glueChain z w N u (x + 1)) (glueChain z w N u (x + 1 + 1)) =
        ∑ x ∈ Finset.range N, D (u x) (u (x + 1)) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.mem_range] at hx
      rw [hvsucc x (by omega), hvsucc (x + 1) (by omega)]
    have hN1 : glueChain z w N u (N + 1 + 1) = w := hvN2
    have hv1' : glueChain z w N u (0 + 1) = p := hv1
    rw [hmid, hvN1, hN1, hv0, hv1']
    ring

/-! ### Lower bound: the partition `{0, 1}` -/

lemma ofReal_le_pathLength {B : Set ℂ} {D : ℂ → ℂ → ℝ}
    (hsymm : ∀ z ∈ B, ∀ w ∈ B, D z w = D w z) {z w : ℂ} (hz : z ∈ B) (hw : w ∈ B)
    (P : Path z w) :
    ENNReal.ofReal (D z w) ≤ pathLength D P := by
  unfold pathLength curveLength
  have hmem : ∀ i : ℕ, min (i : ℝ) 1 ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨le_min (Nat.cast_nonneg _) zero_le_one, min_le_right _ _⟩
  have hmono : Monotone (fun i : ℕ => min (i : ℝ) 1) := fun i j hij =>
    min_le_min_right _ (Nat.cast_le.2 hij)
  refine le_iSup_of_le (1, ⟨fun i : ℕ => min (i : ℝ) 1, hmono, hmem⟩) ?_
  rw [Finset.sum_range_one]
  apply le_of_eq
  congr 1
  simp [hsymm z hz w hw]

/-! ### Short paths from the countable code -/

lemma exists_short_path {c : ℂ} {r : ℝ} {q : ℕ → ↥(ball c r)} {d : C(Win (ball c r), ℝ)}
    (hq : DenseRange q)
    (hself : ∀ z ∈ ball c r, decoderOn (ball c r) d z z = 0)
    (hsymm : ∀ z ∈ ball c r, ∀ w ∈ ball c r, decoderOn (ball c r) d z w = decoderOn (ball c r) d w z)
    (htri : ∀ x ∈ ball c r, ∀ y ∈ ball c r, ∀ u ∈ ball c r,
      decoderOn (ball c r) d x u ≤ decoderOn (ball c r) d x y + decoderOn (ball c r) d y u)
    (hV : V2 (ball c r) (decoderOn (ball c r) d))
    (hlen : ∀ i k : ℕ, ∃ j : ℕ, i ≤ j ∧ ∀ n a b : ℕ,
      (q a : ℂ) ∈ expK c r i → (q b : ℂ) ∈ expK c r i → GoodChain c r q d j k n a b)
    {z w : ℂ} (hz : z ∈ ball c r) (hw : w ∈ ball c r) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Path z w, (∀ t, P t ∈ ball c r) ∧
      pathLength (decoderOn (ball c r) d) P ≤ ENNReal.ofReal (decoderOn (ball c r) d z w + ε) := by
  have hsep := sep_of_V2 hV
  have hcont := continuousOn_decoderOn d
  obtain ⟨i0z, hi0z⟩ := exists_eventually_mem_inner hz
  obtain ⟨i0w, hi0w⟩ := exists_eventually_mem_inner hw
  obtain ⟨I, hzU, hwU⟩ : ∃ I : ℕ, z ∈ ball c (r - 1 / ((I : ℝ) + 2)) ∧
      w ∈ ball c (r - 1 / ((I : ℝ) + 2)) :=
    ⟨max i0z i0w, hi0z _ (le_max_left _ _), hi0w _ (le_max_right _ _)⟩
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show (0 : ℝ) < ε / 8 by positivity)
  obtain ⟨J, hIJ, hJ⟩ := hlen I k
  have hUB : ball c (r - 1 / ((I : ℝ) + 2)) ⊆ ball c r := by
    apply Metric.ball_subset_ball
    have : (0 : ℝ) < 1 / ((I : ℝ) + 2) := by positivity
    linarith
  have hnear : ∀ p ∈ ball c (r - 1 / ((I : ℝ) + 2)), ∀ δ > 0, ∃ a : ℕ,
      (q a : ℂ) ∈ ball c (r - 1 / ((I : ℝ) + 2)) ∧ dist (q a : ℂ) p < δ := by
    intro p hpU δ hδ
    have hpB : p ∈ ball c r := hUB hpU
    have hopen : IsOpen ((Subtype.val : ↥(ball c r) → ℂ) ⁻¹'
        (ball c (r - 1 / ((I : ℝ) + 2)) ∩ ball p δ)) :=
      (isOpen_ball.inter isOpen_ball).preimage continuous_subtype_val
    obtain ⟨a, ha⟩ := hq.exists_mem_open hopen ⟨⟨p, hpB⟩, hpU, mem_ball_self hδ⟩
    exact ⟨a, ha.1, ha.2⟩
  -- endpoints: for each mesh `1/(n+1)`, nearby `q`-points with small decoder distance
  have hedge : ∀ n : ℕ, ∃ a b : ℕ, (q a : ℂ) ∈ ball c (r - 1 / ((I : ℝ) + 2)) ∧
      (q b : ℂ) ∈ ball c (r - 1 / ((I : ℝ) + 2)) ∧
      decoderOn (ball c r) d z (q a) ≤ 1 / ((n : ℝ) + 1) ∧
      decoderOn (ball c r) d (q b) w ≤ 1 / ((n : ℝ) + 1) ∧
      decoderOn (ball c r) d z (q a) < ε / 8 ∧ decoderOn (ball c r) d (q b) w < ε / 8 := by
    intro n
    have hm : (0 : ℝ) < min (1 / ((n : ℝ) + 1)) (ε / 8) := lt_min (by positivity) (by positivity)
    obtain ⟨δ1, hδ1, hs1⟩ := decoder_small_near hself hz hm
    obtain ⟨δ2, hδ2, hs2⟩ := decoder_small_near hself hw hm
    obtain ⟨a, haU, ha⟩ := hnear z hzU δ1 hδ1
    obtain ⟨b, hbU, hb⟩ := hnear w hwU δ2 hδ2
    have hza := hs1 (q a : ℂ) (q a).2 ha
    have hwb := hs2 (q b : ℂ) (q b).2 hb
    refine ⟨a, b, haU, hbU, le_trans hza.le (min_le_left _ _), ?_,
      lt_of_lt_of_le hza (min_le_right _ _), ?_⟩
    · rw [hsymm (q b : ℂ) (q b).2 w hw]
      exact le_trans hwb.le (min_le_left _ _)
    · rw [hsymm (q b : ℂ) (q b).2 w hw]
      exact lt_of_lt_of_le hwb (min_le_right _ _)
  -- the chain from `z` to `w` through `expK J`
  have hchain : ∀ n : ℕ, ∃ N : ℕ, ∃ v : ℕ → ℂ, v 0 = z ∧ v N = w ∧
      (∀ t ≤ N, v t ∈ expK c r J) ∧ (∀ t < N, decoderOn (ball c r) d (v t) (v (t + 1)) ≤
        1 / ((n : ℝ) + 1)) ∧
      chainSum (decoderOn (ball c r) d) v N ≤ decoderOn (ball c r) d z w + ε := by
    intro n
    obtain ⟨a, b, haU, hbU, hza, hwb, hza2, hwb2⟩ := hedge n
    obtain ⟨N', u, hu0, huN, huJ, humesh, husum⟩ :=
      goodChain_to_nat (hJ n a b (ball_sub_expK' c r I haU) (ball_sub_expK' c r I hbU))
    obtain ⟨v, hv0, hvN, hvu, hvmesh, hvsum⟩ :=
      chain_glue (D := decoderOn (ball c r) d) (z := z) (w := w) (p := (q a : ℂ))
        (p' := (q b : ℂ)) (μ := 1 / ((n : ℝ) + 1)) hu0 huN humesh hza hwb
    have hzK : z ∈ expK c r J := expK_mono' c r hIJ (ball_sub_expK' c r I hzU)
    have hwK : w ∈ expK c r J := expK_mono' c r hIJ (ball_sub_expK' c r I hwU)
    refine ⟨N' + 2, v, hv0, hvN, ?_, hvmesh, ?_⟩
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        rw [hv0]
        exact hzK
      by_cases h2 : t = N' + 2
      · subst h2
        rw [hvN]
        exact hwK
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      rw [hvu s (by omega)]
      exact huJ s (by omega)
    · have hA := htri (q a : ℂ) (q a).2 z hz (q b : ℂ) (q b).2
      have hB := htri z hz w hw (q b : ℂ) (q b).2
      have hC := hsymm (q a : ℂ) (q a).2 z hz
      have hD := hsymm (q b : ℂ) (q b).2 w hw
      linarith [hvsum, husum, hza2, hwb2, hk]
  obtain ⟨P, hPK, hPL⟩ := exists_path_of_fine_chains (B := ball c r) (K := expK c r J)
    (x := z) (y := w) (L := decoderOn (ball c r) d z w + ε)
    (by linarith [dist_nonneg_of_clauses hself hsymm htri hz hw])
    (isCompact_expK c r J) (expK_subset c r J) hself hsymm htri hsep hcont hV hchain
  exact ⟨P, fun t => expK_subset c r J (hPK t), hPL⟩

/-! ### The reverse implication -/

/-- **The chain code gives the length clause** (ruling 236, section 6, reverse implication). -/
theorem isLengthMetricOn_of_chainCode {c : ℂ} {r : ℝ} {q : ℕ → ↥(ball c r)}
    {d : C(Win (ball c r), ℝ)} (hq : DenseRange q) (hcl : d ∈ clausesSet (ball c r))
    (hcode : d ∈ codeSet c r) (hlen : d ∈ lengthCodeSet c r q) :
    IsLengthMetricOn (ball c r) (decoderOn (ball c r) d) := by
  obtain ⟨hself, hsymm, htri⟩ : (∀ z ∈ ball c r, decoderOn (ball c r) d z z = 0) ∧
      (∀ z ∈ ball c r, ∀ w ∈ ball c r, decoderOn (ball c r) d z w = decoderOn (ball c r) d w z) ∧
      (∀ x ∈ ball c r, ∀ y ∈ ball c r, ∀ u ∈ ball c r,
        decoderOn (ball c r) d x u ≤ decoderOn (ball c r) d x y + decoderOn (ball c r) d y u) := hcl
  have hlen' : ∀ i k : ℕ, ∃ j : ℕ, i ≤ j ∧ ∀ n a b : ℕ,
      (q a : ℂ) ∈ expK c r i → (q b : ℂ) ∈ expK c r i → GoodChain c r q d j k n a b := hlen
  have hV : V2 (ball c r) (decoderOn (ball c r) d) :=
    V2_of_codeSet ((mem_codeSet_iff c r d).1 hcode)
  refine ⟨hself, sep_of_V2 hV, hsymm, htri, continuousOn_decoderOn d,
    (isOpen_iff_of_V2 isOpen_ball (continuousOn_decoderOn d) hself).2 hV, ?_⟩
  intro z hz w hw
  apply le_antisymm
  · exact le_iInf fun P => le_iInf fun hP => ofReal_le_pathLength hsymm hz hw P
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨P, hPB, hPL⟩ := exists_short_path hq hself hsymm htri hV hlen' hz hw
      (ε := (ε : ℝ)) (NNReal.coe_pos.2 hε)
    calc internalMetric (decoderOn (ball c r) d) (ball c r) z w
        ≤ pathLength (decoderOn (ball c r) d) P := iInf₂_le P hPB
      _ ≤ ENNReal.ofReal (decoderOn (ball c r) d z w + ε) := hPL
      _ = ENNReal.ofReal (decoderOn (ball c r) d z w) + ε := by
          rw [ENNReal.ofReal_add (dist_nonneg_of_clauses hself hsymm htri hz hw)
            (NNReal.coe_nonneg ε), ENNReal.ofReal_coe_nnreal]

end HarmonicBalls.FirstPassS11ahLengthChainReverse
