import HarmonicBalls.Proofs.Sec6.MeasurePushforwardJoint
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-! # Compact approximation of a full-mass set

The compact exhaustion used in the fine-support argument is obtained from inner
regularity and the first Borel–Cantelli lemma.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter
open scoped ENNReal

/-- Compact sets with summable missing masses have an increasing sequence of
compact tail intersections whose union has full mass in the ambient set. -/
theorem compact_tail_intersections_full_mass {μ : Measure ℂ} {A : Set ℂ}
    (K : ℕ → Set ℂ) (hK : ∀ n, IsCompact (K n))
    (hsum : ∑' n, μ (A \ K n) ≠ ∞) :
    ∃ L : ℕ → Set ℂ, (∀ n, IsCompact (L n)) ∧ Monotone L ∧
      (∀ n, L n ⊆ K n) ∧ μ (A \ ⋃ n, L n) = 0 := by
  let L : ℕ → Set ℂ := fun m => ⋂ n ≥ m, K n
  refine ⟨L, ?_, ?_, ?_, ?_⟩
  · intro m
    apply (hK m).of_isClosed_subset
    · exact isClosed_iInter fun n => isClosed_iInter fun _ => (hK n).isClosed
    · intro x hx
      exact (mem_iInter.mp (mem_iInter.mp hx m) le_rfl)
  · intro m n hmn x hx
    simp only [L, mem_iInter] at hx ⊢
    exact fun j hj => hx j (hmn.trans hj)
  · intro n x hx
    exact mem_iInter.mp (mem_iInter.mp hx n) le_rfl
  · apply measure_mono_null _ (measure_setOfPred_frequently_eq_zero hsum)
    intro x hx
    have hA : x ∈ A := hx.1
    have hn : ∀ n, x ∉ L n := by simpa using hx.2
    change ∃ᶠ n in atTop, x ∈ A \ K n
    rw [frequently_atTop]
    intro m
    have hnot := hn m
    simp only [L, mem_iInter, not_forall] at hnot
    obtain ⟨n, hn, hxn⟩ := hnot
    exact ⟨n, hn, hA, hxn⟩

/-- Summably small measurable exceptions admit compact subsets of their
complements whose increasing tail intersections have full ambient mass. -/
theorem compact_full_mass_of_summable_exceptions {μ : Measure ℂ}
    {A : Set ℂ} (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (Y : ℕ → Set ℂ) (hY : ∀ n, MeasurableSet (Y n))
    (hsum : ∑' n, μ (Y n) ≠ ∞) :
    ∃ K L : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ A \ Y n) ∧ (∀ n, IsCompact (L n)) ∧ Monotone L ∧
      (∀ n, L n ⊆ K n) ∧ μ (A \ ⋃ n, L n) = 0 := by
  classical
  have hex (n : ℕ) : ∃ K : Set ℂ, K ⊆ A \ Y n ∧ IsCompact K ∧
      μ ((A \ Y n) \ K) < (2⁻¹ : ℝ≥0∞) ^ n := by
    apply (hA.diff (hY n)).exists_isCompact_sdiff_lt
    · exact ne_top_of_le_ne_top hAfin (measure_mono sdiff_subset)
    · exact pow_ne_zero _ (by simp)
  choose K hsub hcomp herr using hex
  have hb (n : ℕ) : μ (A \ K n) ≤ μ (Y n) + (2⁻¹ : ℝ≥0∞) ^ n := by
    calc
      μ (A \ K n) ≤ μ (Y n ∪ ((A \ Y n) \ K n)) := by
        apply measure_mono
        intro x hx
        by_cases hy : x ∈ Y n
        · exact Or.inl hy
        · exact Or.inr ⟨⟨hx.1, hy⟩, hx.2⟩
      _ ≤ μ (Y n) + μ ((A \ Y n) \ K n) := measure_union_le _ _
      _ ≤ μ (Y n) + (2⁻¹ : ℝ≥0∞) ^ n := by gcongr; exact (herr n).le
  have htotal : ∑' n, μ (A \ K n) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hb)
    rw [ENNReal.tsum_add, ENNReal.tsum_geometric_two]
    exact ENNReal.add_ne_top.mpr ⟨hsum, by simp⟩
  obtain ⟨L, hLc, hLm, hLK, hfull⟩ :=
    compact_tail_intersections_full_mass K hcomp htotal
  exact ⟨K, L, hcomp, hsub, hLc, hLm, hLK, hfull⟩

/-- The dyadic mass bounds from the good-annulus contradiction give the
summability needed for the compact full-mass construction. -/
theorem compact_full_mass_of_dyadic_exceptions {μ : Measure ℂ}
    {A : Set ℂ} (hA : MeasurableSet A) (hAfin : μ A ≠ ∞)
    (Y : ℕ → Set ℂ) (hY : ∀ n, MeasurableSet (Y n))
    (hsmall : ∀ n, μ (Y n) ≤ (2⁻¹ : ℝ≥0∞) ^ n * μ A) :
    ∃ K L : ℕ → Set ℂ, (∀ n, IsCompact (K n)) ∧
      (∀ n, K n ⊆ A \ Y n) ∧ (∀ n, IsCompact (L n)) ∧ Monotone L ∧
      (∀ n, L n ⊆ K n) ∧ μ (A \ ⋃ n, L n) = 0 := by
  apply compact_full_mass_of_summable_exceptions hA hAfin Y hY
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hsmall)
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric_two]
  exact ENNReal.mul_ne_top (by simp) hAfin

end HarmonicBalls.Section6
