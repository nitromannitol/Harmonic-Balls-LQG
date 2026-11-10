import HarmonicBalls.FirstPass.S11ac.CountableChain
import HarmonicBalls.FirstPass.S11ac.Cost
import HarmonicBalls.FirstPass.S11ac.Finite

/-! # The punctured-ball metric decoder, generic core (fp-S11ac, owner z6)

Piece costs `κ_j · M_j(z, w)` on the piece `Dp j`, `⊤` off it; the decoder `psiC` is the countable chain infimum
(`CountableChain`) with vertices in a countable set `Q ∪ {x, y}`, made real by `toReal`. Its identity with
`ofReal β0 · internalMetric D X x y` follows from `chainInf_eq`, `kappaC_eq_of_identity` and `internalMetric_lt_top_of_pieces`.
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal Classical

/-- The cost of one piece step from `z` to `w`: `κ_j · ofReal (M ω j z w)` when both lie in the piece `Dp j`. -/
noncomputable def pieceCost {Ω' : Type*} (Dp : ℕ → Set ℂ) (M : Ω' → ℕ → ℂ → ℂ → ℝ) (c : ℕ → ℕ → ℂ)
    (r : ℕ → ℕ → ℝ) (L : ℕ → List ℕ) (ω : Ω') (j : ℕ) (z w : ℂ) : ℝ≥0∞ :=
  if z ∈ Dp j ∧ w ∈ Dp j then kappaC M c r L j ω * ENNReal.ofReal (M ω j z w) else ⊤

theorem pieceCost_measurable {Ω' : Type*} [MeasurableSpace Ω'] {Dp : ℕ → Set ℂ}
    {M : Ω' → ℕ → ℂ → ℂ → ℝ} (hM : ∀ a z w, Measurable fun ω => M ω a z w) (c : ℕ → ℕ → ℂ)
    (r : ℕ → ℕ → ℝ) (L : ℕ → List ℕ) (j : ℕ) (z w : ℂ) :
    Measurable fun ω => pieceCost Dp M c r L ω j z w := by
  by_cases hz : z ∈ Dp j ∧ w ∈ Dp j
  · have e : (fun ω => pieceCost Dp M c r L ω j z w) =
        fun ω => kappaC M c r L j ω * ENNReal.ofReal (M ω j z w) := by
      funext ω
      unfold pieceCost
      split_ifs
      rfl
    rw [e]
    exact (kappaC_measurable hM c r L j).mul (ENNReal.measurable_ofReal.comp (hM j z w))
  · have e : (fun ω => pieceCost Dp M c r L ω j z w) = fun _ => ⊤ := by
      funext ω
      unfold pieceCost
      split_ifs
      rfl
    rw [e]
    exact measurable_const

/-- The generic decoder: the countable chain infimum with vertices in `Q ∪ {x, y}`, made real. -/
noncomputable def psiC {Ω' : Type*} (Dp : ℕ → Set ℂ) (M : Ω' → ℕ → ℂ → ℂ → ℝ) (c : ℕ → ℕ → ℂ)
    (r : ℕ → ℕ → ℝ) (L : ℕ → List ℕ) (Q : Set ℂ) (x y : ℂ) (ω : Ω') : ℝ :=
  (⨅ σ : CIdx (Q ∪ {x, y}), cChain (pieceCost Dp M c r L ω) Dp x y σ).toReal

theorem psiC_measurable {Ω' : Type*} [MeasurableSpace Ω'] {Dp : ℕ → Set ℂ}
    {M : Ω' → ℕ → ℂ → ℂ → ℝ} (hM : ∀ a z w, Measurable fun ω => M ω a z w) (c : ℕ → ℕ → ℂ)
    (r : ℕ → ℕ → ℝ) (L : ℕ → List ℕ) {Q : Set ℂ} (hQ : Q.Countable) (x y : ℂ) :
    Measurable (psiC Dp M c r L Q x y) := by
  have hc : (Q ∪ {x, y}).Countable := hQ.union (Set.toFinite _).countable
  exact ENNReal.measurable_toReal.comp
    (measurable_iInf_cChain (fun j z w => pieceCost_measurable hM c r L j z w) Dp hc x y)

/-- **Identity of the generic decoder.** Let `X` be open and path-connected, covered by open pieces `Dp j ⊆ X` with
overlap chains `L j`, and let the masses satisfy the local identities on each piece with constants `β`. Then for
`x, y ∈ X`, `ofReal (psiC ω) = ofReal (β 0) * internalMetric D X x y`. -/
theorem psiC_identity {Ω' : Type*} (Dp : ℕ → Set ℂ) (hopen : ∀ j, IsOpen (Dp j))
    (M : Ω' → ℕ → ℂ → ℂ → ℝ) (c : ℕ → ℕ → ℂ) (r : ℕ → ℕ → ℝ)
    (hpair : ∀ a b, 0 < r a b ∧ ((Dp a ∩ Dp b).Nonempty → ball (c a b) (r a b) ⊆ Dp a ∩ Dp b))
    (L : ℕ → List ℕ) (hL : ∀ j, OvChain Dp 0 (L j) ∧ lastOr 0 (L j) = j)
    {X : Set ℂ} (hXo : IsOpen X) (hXpc : IsPathConnected X) (hDpX : ∀ j, Dp j ⊆ X)
    (hcov : X ⊆ ⋃ j, Dp j) {Q : Set ℂ} (hQd : X ⊆ closure Q)
    (ω : Ω') {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (β : ℕ → ℝ) (hβ : ∀ a, 0 < β a)
    (hid : ∀ a, ∀ z ∈ Dp a, ∀ w ∈ Dp a,
      ENNReal.ofReal (M ω a z w) = ENNReal.ofReal (β a) * internalMetric D (Dp a) z w)
    {x y : ℂ} (hx : x ∈ X) (hy : y ∈ X) :
    ENNReal.ofReal (psiC Dp M c r L Q x y ω) = ENNReal.ofReal (β 0) * internalMetric D X x y := by
  have hQ'd : X ⊆ closure (Q ∪ {x, y}) := hQd.trans (closure_mono (subset_union_left))
  have hxQ : x ∈ Q ∪ {x, y} := Or.inr (by simp)
  have hyQ : y ∈ Q ∪ {x, y} := Or.inr (by simp)
  have hpieceFin : ∀ j z w, z ∈ Dp j → w ∈ Dp j → internalMetric D (Dp j) z w < ⊤ := by
    intro j z w hz hw
    refine lt_top_iff_ne_top.2 fun h => ENNReal.ofReal_ne_top (?_ : ENNReal.ofReal (M ω j z w) = ⊤)
    rw [hid j z hz w hw, h, ENNReal.mul_top (by simpa using hβ j)]
  have hfin := internalMetric_lt_top_of_pieces hD hXo hXpc hDpX hopen hcov hpieceFin hx hy
  have hcost : ∀ j z w, z ∈ Dp j → w ∈ Dp j →
      pieceCost Dp M c r L ω j z w = ENNReal.ofReal (β 0) * internalMetric D (Dp j) z w := by
    intro j z w hz hw
    unfold pieceCost
    split_ifs with h
    · have hk := kappaC_eq_of_identity Dp hopen M c r hpair L hL ω hD hnonneg β hβ hid j
      rw [hk, hid j z hz w hw, ← mul_assoc, ← ENNReal.ofReal_mul (div_nonneg (hβ 0).le (hβ j).le),
        div_mul_cancel₀ _ (hβ j).ne']
    · exact absurd ⟨hz, hw⟩ h
  have hchain : (⨅ σ : CIdx (Q ∪ {x, y}), cChain (pieceCost Dp M c r L ω) Dp x y σ) =
      ENNReal.ofReal (β 0) * internalMetric D X x y := by
    rw [← chainInf_eq_iInf_cChain _ Dp hxQ hyQ]
    exact chainInf_eq hD hXo hDpX hopen hcov hQ'd
      (ENNReal.ofReal_pos.2 (hβ 0)).ne' ENNReal.ofReal_ne_top hcost hy
  unfold psiC
  rw [hchain, ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)]

end HarmonicBalls.S11ac
