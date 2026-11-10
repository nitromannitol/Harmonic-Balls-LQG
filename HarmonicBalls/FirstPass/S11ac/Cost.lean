import HarmonicBalls.FirstPass.S11ac.Constants
import HarmonicBalls.FirstPass.S11ac.RatioLimit

/-! # Piece constants `κ_j` (fp-S11ac, owner z6)

For open pieces `Dp j`, pair data `c a b`, `r a b` (a disk inside `Dp a ∩ Dp b` for overlapping pairs), and a family
of overlap chains `L j` from `0` to `j`, the piece constant is `κ_j(ω) = ∏ ratioLim` along `L j`. It is measurable in
the parameter and, when the local identities hold on every piece, equals `ofReal (β 0 / β j)`.
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology MeasureTheory Metric
open scoped ENNReal

/-- Pair data: a centre and a radius for each pair of pieces, with a disk inside the intersection when the pieces
overlap. -/
theorem exists_pair_data (Dp : ℕ → Set ℂ) (hopen : ∀ j, IsOpen (Dp j)) :
    ∃ c : ℕ → ℕ → ℂ, ∃ r : ℕ → ℕ → ℝ,
      ∀ a b, 0 < r a b ∧ ((Dp a ∩ Dp b).Nonempty → ball (c a b) (r a b) ⊆ Dp a ∩ Dp b) := by
  have h : ∀ a b, ∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ ((Dp a ∩ Dp b).Nonempty → ball c r ⊆ Dp a ∩ Dp b) := by
    intro a b
    by_cases hne : (Dp a ∩ Dp b).Nonempty
    · obtain ⟨z, hz⟩ := hne
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 ((hopen a).inter (hopen b)) z hz
      exact ⟨z, r, hr, fun _ => hsub⟩
    · exact ⟨0, 1, one_pos, fun h' => absurd h' hne⟩
  choose c r hr hsub using h
  exact ⟨c, r, fun a b => ⟨hr a b, hsub a b⟩⟩

/-- The product of the ratios along a list chain, as a function of the parameter. -/
noncomputable def kappaC {Ω' : Type*} (M : Ω' → ℕ → ℂ → ℂ → ℝ) (c : ℕ → ℕ → ℂ) (r : ℕ → ℕ → ℝ)
    (L : ℕ → List ℕ) (j : ℕ) (ω : Ω') : ℝ≥0∞ :=
  ratioProd (fun a b => ratioLim M a b (c a b) (r a b) ω) 0 (L j)

theorem ratioProd_measurable {Ω' : Type*} [MeasurableSpace Ω'] {M : Ω' → ℕ → ℂ → ℂ → ℝ}
    (hM : ∀ a z w, Measurable fun ω => M ω a z w) (c : ℕ → ℕ → ℂ) (r : ℕ → ℕ → ℝ) (L : List ℕ) (a : ℕ) :
    Measurable fun ω => ratioProd (fun a b => ratioLim M a b (c a b) (r a b) ω) a L := by
  induction L generalizing a with
  | nil => exact measurable_const
  | cons b L ih =>
    exact (ratioLim_measurable hM a b (c a b) (r a b)).mul (ih b)

theorem kappaC_measurable {Ω' : Type*} [MeasurableSpace Ω'] {M : Ω' → ℕ → ℂ → ℂ → ℝ}
    (hM : ∀ a z w, Measurable fun ω => M ω a z w) (c : ℕ → ℕ → ℂ) (r : ℕ → ℕ → ℝ) (L : ℕ → List ℕ) (j : ℕ) :
    Measurable (kappaC M c r L j) :=
  ratioProd_measurable hM c r (L j) 0

/-- **Piece constants.** Let `L j` be overlap chains from `0` to `j`. If on every piece `Dp a` the masses are
`ofReal (β a)` times the internal metric `D` (`D` a nonnegative length metric), then `κ_j = ofReal (β 0 / β j)`. -/
theorem kappaC_eq_of_identity {Ω' : Type*} (Dp : ℕ → Set ℂ) (hopen : ∀ j, IsOpen (Dp j))
    (M : Ω' → ℕ → ℂ → ℂ → ℝ) (c : ℕ → ℕ → ℂ) (r : ℕ → ℕ → ℝ)
    (hpair : ∀ a b, 0 < r a b ∧ ((Dp a ∩ Dp b).Nonempty → ball (c a b) (r a b) ⊆ Dp a ∩ Dp b))
    (L : ℕ → List ℕ) (hL : ∀ j, OvChain Dp 0 (L j) ∧ lastOr 0 (L j) = j)
    (ω : Ω') {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (hnonneg : ∀ x y, 0 ≤ D x y)
    (β : ℕ → ℝ) (hβ : ∀ a, 0 < β a)
    (hid : ∀ a, ∀ z ∈ Dp a, ∀ w ∈ Dp a,
      ENNReal.ofReal (M ω a z w) = ENNReal.ofReal (β a) * internalMetric D (Dp a) z w) (j : ℕ) :
    kappaC M c r L j ω = ENNReal.ofReal (β 0 / β j) := by
  have hR : ∀ a b, (Dp a ∩ Dp b).Nonempty →
      ratioLim M a b (c a b) (r a b) ω = ENNReal.ofReal (β a / β b) := fun a b hab =>
    ratioLim_eq_of_identity M ω a b hD hnonneg (hopen a) (hopen b) (hpair a b).1 ((hpair a b).2 hab)
      (hβ a) (hβ b) (fun z hz w hw => hid a z hz w hw) (fun z hz w hw => hid b z hz w hw)
  have key := ratioProd_eq_of_chain Dp hβ hR (L j) 0 (hL j).1
  unfold kappaC
  rw [key, (hL j).2]

end HarmonicBalls.S11ac
