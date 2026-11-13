import HarmonicBalls.FirstPass.Phase2.RootedLocalAgreementEvent

/-!
# Fine chains at the points of `S` from the chain event

`eventChains S K d` (the event `A2` of `RootedLocalAgreementEvent`) says that for every pair `x, y ∈ S` and every
rational `ε > 0` there is a window `K n` such that for every rational mesh `δ > 0` some chain through points of `S`
inside `K n`, with steps shorter than `δ`, has `d`-length at most `d x y + ε`.

`chains_of_eventChains` turns this into the pairwise fine-chain property of the library's gluing lemma
(`LatticeProb.Topology.HasFineChainsAt D d x y`, stated here unfolded): extended constantly beyond the last index,
the chains become sequences `ℕ → ℂ`; real `ε` and `δ` are bounded below by rational ones.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

variable {Ω : Type*}

/-- A positive extended real dominates `ofReal q` for some positive rational `q`. -/
theorem exists_pos_rat_ofReal_le {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ q : ℚ, 0 < q ∧ ENNReal.ofReal q ≤ ε := by
  rcases eq_or_ne ε ⊤ with rfl | hne
  · exact ⟨1, one_pos, by simp⟩
  · obtain ⟨q, hq0, hq⟩ := exists_rat_btwn (ENNReal.toReal_pos hε.ne' hne)
    exact ⟨q, by exact_mod_cast hq0, ENNReal.ofReal_le_of_le_toReal hq.le⟩

/-- **Fine chains at the points of `S`.** If `o` lies in the chain event of `d` on `S` with compact windows
`K n ⊆ D`, then for `x, y ∈ S` the function `d o` has fine chains at `(x, y)` relative to `D`. -/
theorem chains_of_eventChains {S D : Set ℂ} {K : ℕ → Set ℂ} (hKc : ∀ n, IsCompact (K n))
    (hKD : ∀ n, K n ⊆ D) {d : Ω → ℂ → ℂ → ℝ≥0∞} {o : Ω} (ho : o ∈ eventChains S K d)
    {x y : ℂ} (hx : x ∈ S) (hy : y ∈ S) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ K' ⊆ D, IsCompact K' ∧ ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∃ m : ℕ → ℂ,
      m 0 = x ∧ m N = y ∧ (∀ i ≤ N, m i ∈ K') ∧ (∀ i < N, dist (m i) (m (i + 1)) < δ) ∧
        ∑ i ∈ Finset.range N, d o (m i) (m (i + 1)) ≤ d o x y + ε := by
  intro ε hε
  obtain ⟨q, hq, hqε⟩ := exists_pos_rat_ofReal_le hε
  obtain ⟨n, hn⟩ := ho x hx y hy q hq
  refine ⟨K n, hKD n, hKc n, fun δ hδ => ?_⟩
  obtain ⟨δ', hδ'0, hδ'⟩ := exists_rat_btwn hδ
  obtain ⟨N, m, hm0, hmN, hmK, hmδ, hmsum⟩ := hn δ' (by exact_mod_cast hδ'0)
  classical
  let m' : ℕ → ℂ := fun i => if h : i < N + 1 then ((m ⟨i, h⟩ : S) : ℂ) else y
  have hm'fin : ∀ i : Fin (N + 1), m' i = (m i : ℂ) := fun i => by
    simp only [m']
    split
    · rfl
    · rename_i h
      exact absurd i.2 h
  refine ⟨N, m', ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : m' 0 = (m 0 : ℂ) := by simpa using hm'fin 0
    rw [h0, hm0]
  · have : m' N = (m (Fin.last N) : ℂ) := hm'fin (Fin.last N)
    rw [this, hmN]
  · intro i hi
    have h : m' i = (m ⟨i, Nat.lt_succ_of_le hi⟩ : ℂ) := hm'fin ⟨i, Nat.lt_succ_of_le hi⟩
    rw [h]
    exact hmK _
  · intro i hi
    have h1 : m' i = (m (Fin.castSucc ⟨i, hi⟩) : ℂ) := hm'fin (Fin.castSucc ⟨i, hi⟩)
    have h2 : m' (i + 1) = (m (Fin.succ ⟨i, hi⟩) : ℂ) := hm'fin (Fin.succ ⟨i, hi⟩)
    rw [h1, h2, dist_eq_norm]
    exact (hmδ ⟨i, hi⟩).trans hδ'
  · calc ∑ i ∈ Finset.range N, d o (m' i) (m' (i + 1))
        = ∑ i : Fin N, d o (m i.castSucc) (m i.succ) := by
          rw [Finset.sum_range]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h1 : m' (i : ℕ) = (m i.castSucc : ℂ) := by simpa using hm'fin i.castSucc
          have h2 : m' ((i : ℕ) + 1) = (m i.succ : ℂ) := by simpa using hm'fin i.succ
          rw [h1, h2]
      _ ≤ d o x y + ENNReal.ofReal q := hmsum
      _ ≤ d o x y + ε := add_le_add le_rfl hqε

end HarmonicBalls
