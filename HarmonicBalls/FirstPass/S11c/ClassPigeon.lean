import HarmonicBalls.FirstPass.S11c.GridK0Connect
import HarmonicBalls.FirstPass.S11c.ProbAssembly

/-!
# Proposition 11.10, the quantitative class choice

In the printed proof of `lemma:mass-diam` (paper lines 3091-3112) one of the four classes
of the level-`N` squares carries mass above `2c` on the event of positive probability `p₀ = P(8c < μ(S₁))`, and this class
has probability at least `p₀ / 4`, uniformly in `N`. That uniformity is what allows the level `N` to be chosen after the
probability `η` of the piece and exterior events. This file proves (i) the deterministic pigeonhole on four classes covering a
set, (ii) the probabilistic form `p₀ ≤ 4 P(X_i)` for some class (the class of largest probability), and (iii) the core of
`gridK0` is nonempty for the class index sets.
-/

open MeasureTheory Set
open scoped ENNReal

namespace HarmonicBalls

/-- Deterministic pigeonhole: if four sets cover `S` and `8c < μ S`, one of them has mass above `2c`. -/
lemma class_of_mass_gt {X : Type*} [MeasurableSpace X] {μ : Measure X} {S : Set X} {C : Fin 4 → Set X}
    {c : ℝ≥0∞} (hcover : S ⊆ ⋃ i, C i) (hS : 8 * c < μ S) : ∃ i : Fin 4, 2 * c < μ (C i) := by
  by_contra h
  simp only [not_exists, not_lt] at h
  have h1 : μ S ≤ ∑ i, μ (C i) := le_trans (measure_mono hcover) (measure_iUnion_fintype_le μ C)
  have h2 : ∑ i, μ (C i) ≤ 8 * c := by
    rw [Fin.sum_univ_four]
    calc μ (C 0) + μ (C 1) + μ (C 2) + μ (C 3) ≤ 2 * c + 2 * c + 2 * c + 2 * c :=
          add_le_add (add_le_add (add_le_add (h 0) (h 1)) (h 2)) (h 3)
      _ = 8 * c := by ring
  exact absurd (lt_of_lt_of_le hS (le_trans h1 h2)) (lt_irrefl _)

/-- Probabilistic pigeonhole with a quantitative bound: some class has probability at least a quarter of
`P(8c < μ(S))`. -/
lemma exists_class_quarter_of_prob {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] (P : Measure Ω)
    (μ : Ω → Measure X) {S : Set X} {C : Fin 4 → Set X} {c : ℝ≥0∞} (hcover : S ⊆ ⋃ i, C i) :
    ∃ i : Fin 4, P {ω | 8 * c < μ ω S} ≤ 4 * P {ω | 2 * c < μ ω (C i)} := by
  have hsub : {ω | 8 * c < μ ω S} ⊆ ⋃ i, {ω | 2 * c < μ ω (C i)} := by
    intro ω hω
    obtain ⟨i, hi⟩ := class_of_mass_gt hcover hω
    exact mem_iUnion.2 ⟨i, hi⟩
  have h1 := le_trans (measure_mono hsub) (measure_iUnion_fintype_le P (fun i => {ω | 2 * c < μ ω (C i)}))
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin 4))
    (fun i => P {ω | 2 * c < μ ω (C i)}) Finset.univ_nonempty
  refine ⟨i, le_trans h1 ?_⟩
  calc ∑ j, P {ω | 2 * c < μ ω (C j)} ≤ ∑ _j : Fin 4, P {ω | 2 * c < μ ω (C i)} :=
        Finset.sum_le_sum (fun j _ => hi j (Finset.mem_univ j))
    _ = 4 * P {ω | 2 * c < μ ω (C i)} := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The core of the grid box, for the class index sets, is nonempty: it contains the free hub pair. -/
lemma gridK0_class_nonempty {h : ℝ} (hh : 0 < h) {p q P₁ P₂ Q₁ Q₂ A₁ A₂ B₁ B₂ : ℤ}
    (hp : p = 0 ∨ p = 1) (hq : q = 0 ∨ q = 1)
    (hP₁ : P₁ % 8 = 0) (hQ₁ : Q₁ % 8 = 0) (hA₁ : A₁ ≤ P₁) (hP₂ : P₂ ≤ A₂) (hB₁ : B₁ ≤ Q₁) (hQ₂ : Q₂ ≤ B₂)
    (hsz : P₁ + 16 ≤ P₂) (hQsz : Q₁ + 16 ≤ Q₂) (hA : A₁ + 16 ≤ A₂) (hB : B₁ + 16 ≤ B₂) :
    (gridK0 h {j : ℤ | j % 2 = p ∧ P₁ ≤ 8 * j ∧ 8 * j + 8 ≤ P₂}
      {k : ℤ | k % 2 = q ∧ Q₁ ≤ 8 * k ∧ 8 * k + 8 ≤ Q₂} A₁ A₂ B₁ B₂).Nonempty := by
  obtain ⟨xh, hxh, hxhX⟩ := exists_free_abscissa hh hp hP₁ hA₁ hP₂ hsz hA
  obtain ⟨yh, hyh, hyhY⟩ := exists_free_abscissa hh hq hQ₁ hB₁ hQ₂ hQsz hB
  refine ⟨⟨xh, yh⟩, ?_⟩
  unfold gridK0 gridBox
  refine ⟨Complex.mem_reProdIm.2 ⟨hxh, hyh⟩, ?_⟩
  intro hmem
  exact hxhX hmem.1

end HarmonicBalls
