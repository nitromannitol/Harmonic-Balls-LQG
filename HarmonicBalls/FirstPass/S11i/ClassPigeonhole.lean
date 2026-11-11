import Mathlib

/-!
# Measure pigeonhole over four classes (Lemma 11.12 replacement, Theorem 2)

Generic measure step of Theorem 2: "The four
classes cover `S_0`, so one deterministic class has total core mass greater than `2c` on a positive-probability subset
of this event." If an event `B` is covered by finitely many events `A c`, one per class `c`, then some class satisfies
`P B ≤ 4 · P (B ∩ A c)`, so `P (B ∩ A c) > 0` whenever `P B > 0`.
-/

open MeasureTheory

namespace FirstPassS11i

/-- Pigeonhole for measures: if the event `B` is covered by the events `A c`, `c ∈ C`, with `#C = 4`, then some `c ∈ C`
satisfies `P B ≤ 4 P (B ∩ A c)`. -/
theorem exists_class_measure_ge {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (B : Set Ω)
    (A : ι → Set Ω) (C : Finset ι) (hC : C.card = 4) (hcov : B ⊆ ⋃ c ∈ C, A c) :
    ∃ c ∈ C, P B ≤ 4 * P (B ∩ A c) := by
  have hne : C.Nonempty := by
    rw [← Finset.card_pos, hC]
    norm_num
  obtain ⟨c, hc, hmax⟩ := Finset.exists_max_image C (fun c => P (B ∩ A c)) hne
  refine ⟨c, hc, ?_⟩
  have hsub : B ⊆ ⋃ d ∈ C, B ∩ A d := by
    intro x hx
    obtain ⟨d, hd, hxd⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact Set.mem_iUnion₂.2 ⟨d, hd, hx, hxd⟩
  calc P B ≤ P (⋃ d ∈ C, B ∩ A d) := measure_mono hsub
    _ ≤ ∑ d ∈ C, P (B ∩ A d) := measure_biUnion_finset_le C _
    _ ≤ ∑ d ∈ C, P (B ∩ A c) := Finset.sum_le_sum hmax
    _ = 4 * P (B ∩ A c) := by
      rw [Finset.sum_const, hC, nsmul_eq_mul]
      norm_num

end FirstPassS11i
