import HarmonicBalls.FirstPass.S11ac.ChainGlue

/-! # Countable index for the piece-chain infimum

`chainInf` takes its infimum over sequences `ℕ → ℂ`, an uncountable index. Measurability of the infimum in a
parameter needs a countable index. Here a piece-chain is a finite tuple: a length `n`, pieces `Fin n → ℕ` and
vertices `Fin (n+1) → Q` with `Q` a countable set containing the endpoints. The infimum over these tuples equals
`chainInf` (Lemma `chainInf_eq_iInf_cChain`).
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology
open scoped ENNReal Classical

/-- Countable index of finite piece-chains with vertices in `Q`: a length `n`, pieces `Fin n → ℕ`, vertices
`Fin (n+1) → Q`. -/
abbrev CIdx (Q : Set ℂ) : Type := Σ n : ℕ, (Fin n → ℕ) × (Fin (n + 1) → Q)

/-- The `k`-th vertex of a countable index (value `0` beyond its length, never used there). -/
noncomputable def CIdx.vtx {Q : Set ℂ} (σ : CIdx Q) (k : ℕ) : ℂ :=
  if h : k < σ.1 + 1 then (σ.2.2 ⟨k, h⟩ : ℂ) else 0

/-- The `i`-th piece of a countable index (value `0` beyond its length, never used there). -/
noncomputable def CIdx.pc {Q : Set ℂ} (σ : CIdx Q) (i : ℕ) : ℕ :=
  if h : i < σ.1 then σ.2.1 ⟨i, h⟩ else 0

/-- Cost of a countable index from `x` to `y`: the sum of the piece costs along the vertices, `⊤` unless the
endpoints are `x`, `y` and consecutive vertices lie in their pieces. -/
noncomputable def cChain (cost : ℕ → ℂ → ℂ → ℝ≥0∞) (Dp : ℕ → Set ℂ) {Q : Set ℂ} (x y : ℂ) (σ : CIdx Q) :
    ℝ≥0∞ :=
  if CIdx.vtx σ 0 = x ∧ CIdx.vtx σ σ.1 = y ∧
      ∀ i < σ.1, CIdx.vtx σ i ∈ Dp (CIdx.pc σ i) ∧ CIdx.vtx σ (i + 1) ∈ Dp (CIdx.pc σ i) then
    ∑ i ∈ Finset.range σ.1, cost (CIdx.pc σ i) (CIdx.vtx σ i) (CIdx.vtx σ (i + 1))
  else ⊤

theorem countable_CIdx {Q : Set ℂ} (hQ : Q.Countable) : Countable (CIdx Q) := by
  have := hQ.to_subtype
  infer_instance

theorem CIdx.vtx_mem {Q : Set ℂ} (σ : CIdx Q) {k : ℕ} (hk : k < σ.1 + 1) : CIdx.vtx σ k ∈ Q := by
  unfold CIdx.vtx
  simp only [hk, dite_true]
  exact (σ.2.2 ⟨k, hk⟩).2

theorem CIdx.vtx_mk {Q : Set ℂ} (n : ℕ) (j : Fin n → ℕ) (v : Fin (n + 1) → Q) {k : ℕ} (hk : k < n + 1) :
    CIdx.vtx (⟨n, (j, v)⟩ : CIdx Q) k = (v ⟨k, hk⟩ : ℂ) := by
  simp only [CIdx.vtx, hk, dite_true]

theorem CIdx.pc_mk {Q : Set ℂ} (n : ℕ) (j : Fin n → ℕ) (v : Fin (n + 1) → Q) {i : ℕ} (hi : i < n) :
    CIdx.pc (⟨n, (j, v)⟩ : CIdx Q) i = j ⟨i, hi⟩ := by
  simp only [CIdx.pc, hi, dite_true]

theorem cChain_pos {Q : Set ℂ} (cost : ℕ → ℂ → ℂ → ℝ≥0∞) (Dp : ℕ → Set ℂ) (x y : ℂ) (σ : CIdx Q)
    (hc : CIdx.vtx σ 0 = x ∧ CIdx.vtx σ σ.1 = y ∧
      ∀ i < σ.1, CIdx.vtx σ i ∈ Dp (CIdx.pc σ i) ∧ CIdx.vtx σ (i + 1) ∈ Dp (CIdx.pc σ i)) :
    cChain cost Dp x y σ =
      ∑ i ∈ Finset.range σ.1, cost (CIdx.pc σ i) (CIdx.vtx σ i) (CIdx.vtx σ (i + 1)) := by
  unfold cChain
  split_ifs
  rfl

theorem cChain_neg {Q : Set ℂ} (cost : ℕ → ℂ → ℂ → ℝ≥0∞) (Dp : ℕ → Set ℂ) (x y : ℂ) (σ : CIdx Q)
    (hc : ¬ (CIdx.vtx σ 0 = x ∧ CIdx.vtx σ σ.1 = y ∧
      ∀ i < σ.1, CIdx.vtx σ i ∈ Dp (CIdx.pc σ i) ∧ CIdx.vtx σ (i + 1) ∈ Dp (CIdx.pc σ i))) :
    cChain cost Dp x y σ = ⊤ := by
  unfold cChain
  split_ifs
  rfl

/-- **Countable form of the chain infimum.** For `x, y ∈ Q`, the infimum of the countable chain costs equals the
infimum over piece-chains with interior vertices in `Q` (`chainInf`). -/
theorem chainInf_eq_iInf_cChain (cost : ℕ → ℂ → ℂ → ℝ≥0∞) (Dp : ℕ → Set ℂ) {Q : Set ℂ} {x y : ℂ}
    (hx : x ∈ Q) (hy : y ∈ Q) :
    chainInf cost Dp Q x y = ⨅ σ : CIdx Q, cChain cost Dp x y σ := by
  refine le_antisymm ?_ ?_
  · unfold chainInf
    refine le_iInf fun σ => ?_
    by_cases hc : CIdx.vtx σ 0 = x ∧ CIdx.vtx σ σ.1 = y ∧
        ∀ i < σ.1, CIdx.vtx σ i ∈ Dp (CIdx.pc σ i) ∧ CIdx.vtx σ (i + 1) ∈ Dp (CIdx.pc σ i)
    · rw [cChain_pos _ _ _ _ _ hc]
      have hQ' : ∀ i, 0 < i → i < σ.1 → CIdx.vtx σ i ∈ Q := fun i _ hi => CIdx.vtx_mem σ (by omega)
      refine iInf_le_of_le σ.1 (iInf_le_of_le (CIdx.pc σ) (iInf_le_of_le (CIdx.vtx σ)
        (iInf_le_of_le ⟨hc.1, hc.2.1, hQ', fun i hi => hc.2.2 i hi⟩ le_rfl)))
    · rw [cChain_neg _ _ _ _ _ hc]
      exact le_top
  · unfold chainInf
    refine le_iInf fun n => le_iInf fun j => le_iInf fun q => le_iInf fun hpc => ?_
    obtain ⟨h0, hn, hQ, hD⟩ := hpc
    have hQk : ∀ k : Fin (n + 1), q k ∈ Q := by
      intro k
      rcases Nat.eq_zero_or_pos (k : ℕ) with hk | hk
      · have : k = 0 := Fin.ext (by simpa using hk)
        subst this
        simpa [h0] using hx
      · rcases Nat.lt_or_ge (k : ℕ) n with hkn | hkn
        · exact hQ k hk hkn
        · have : (k : ℕ) = n := by have := k.2; omega
          have : k = Fin.last n := Fin.ext (by simpa using this)
          subst this
          simpa [hn] using hy
    let σ : CIdx Q := ⟨n, (fun i : Fin n => j i, fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))⟩
    refine iInf_le_of_le σ ?_
    have hc : CIdx.vtx σ 0 = x ∧ CIdx.vtx σ σ.1 = y ∧
        ∀ i < σ.1, CIdx.vtx σ i ∈ Dp (CIdx.pc σ i) ∧ CIdx.vtx σ (i + 1) ∈ Dp (CIdx.pc σ i) := by
      refine ⟨?_, ?_, fun i hi => ?_⟩
      · have h := CIdx.vtx_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
          (k := 0) (Nat.succ_pos n)
        simpa [σ, h0] using h
      · have h := CIdx.vtx_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
          (k := n) (Nat.lt_succ_self n)
        simpa [σ, hn] using h
      · have hi' : i < n := hi
        have h1 := CIdx.vtx_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
          (k := i) (by omega)
        have h2 := CIdx.vtx_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
          (k := i + 1) (by omega)
        have hp := CIdx.pc_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
          (i := i) hi'
        simp only [σ] at h1 h2 hp ⊢
        rw [h1, h2, hp]
        exact hD i hi'
    rw [cChain_pos _ _ _ _ _ hc]
    refine le_of_eq (Finset.sum_congr rfl fun i hi => ?_)
    have hi' : i < n := Finset.mem_range.1 hi
    have h1 := CIdx.vtx_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
      (k := i) (by omega)
    have h2 := CIdx.vtx_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
      (k := i + 1) (by omega)
    have hp := CIdx.pc_mk (Q := Q) n (fun i : Fin n => j i) (fun k : Fin (n + 1) => (⟨q k, hQk k⟩ : Q))
      (i := i) hi'
    simp only [σ] at h1 h2 hp ⊢
    rw [h1, h2, hp]

/-- Measurability in a parameter of the countable chain infimum, when each piece cost is measurable. -/
theorem measurable_iInf_cChain {Ω' : Type*} [MeasurableSpace Ω'] {cost : Ω' → ℕ → ℂ → ℂ → ℝ≥0∞}
    (hcost : ∀ j z w, Measurable fun ω => cost ω j z w) (Dp : ℕ → Set ℂ) {Q : Set ℂ} (hQ : Q.Countable)
    (x y : ℂ) : Measurable fun ω => ⨅ σ : CIdx Q, cChain (cost ω) Dp x y σ := by
  have := countable_CIdx hQ
  refine Measurable.iInf fun σ => ?_
  by_cases hc : CIdx.vtx σ 0 = x ∧ CIdx.vtx σ σ.1 = y ∧
      ∀ i < σ.1, CIdx.vtx σ i ∈ Dp (CIdx.pc σ i) ∧ CIdx.vtx σ (i + 1) ∈ Dp (CIdx.pc σ i)
  · have e : (fun ω => cChain (cost ω) Dp x y σ) =
        fun ω => ∑ i ∈ Finset.range σ.1, cost ω (CIdx.pc σ i) (CIdx.vtx σ i) (CIdx.vtx σ (i + 1)) :=
      funext fun ω => cChain_pos _ _ _ _ _ hc
    rw [e]
    exact Finset.measurable_sum _ fun i _ => hcost (CIdx.pc σ i) (CIdx.vtx σ i) (CIdx.vtx σ (i + 1))
  · have e : (fun ω => cChain (cost ω) Dp x y σ) = fun _ => ⊤ :=
      funext fun ω => cChain_neg _ _ _ _ _ hc
    rw [e]
    exact measurable_const

end HarmonicBalls.S11ac
