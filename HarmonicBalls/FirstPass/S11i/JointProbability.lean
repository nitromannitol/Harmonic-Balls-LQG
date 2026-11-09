import Mathlib

/-!
# Joint probability at one level (Lemma 11.12 replacement, Theorem 2)

Generic measure step of Theorem 2 (`notes/fp-gaps/G-11-12.md`, section 3, "Proof of unconditional positivity"): "Choose
one deterministic `n` such that the mass event and `max_S diam_D(H_S) < ε/16` have joint probability at least `p/2`."
If an event `A` satisfies `p ≤ P A` for some `p > 0`, and the events `B n` hold eventually almost surely, then some single
`n` satisfies `P (A ∩ B n) ≥ p/2`. Only measure theory is used.
-/

open MeasureTheory Filter Topology Set

namespace FirstPassS11i

/-- The tail intersection `⋂_{n ≥ m} B n`. -/
def tailInter {Ω : Type*} (B : ℕ → Set Ω) (m : ℕ) : Set Ω :=
  ⋂ n, ⋂ (_ : m ≤ n), B n

lemma measurableSet_tailInter {Ω : Type*} [MeasurableSpace Ω] {B : ℕ → Set Ω} (hB : ∀ n, MeasurableSet (B n))
    (m : ℕ) : MeasurableSet (tailInter B m) :=
  MeasurableSet.iInter fun n => MeasurableSet.iInter fun _ => hB n

lemma tailInter_mono {Ω : Type*} (B : ℕ → Set Ω) : Monotone (tailInter B) := by
  intro m m' hmm ω hω
  simp only [tailInter, mem_iInter] at hω ⊢
  intro n hn
  exact hω n (le_trans hmm hn)

lemma tailInter_subset {Ω : Type*} (B : ℕ → Set Ω) (m : ℕ) : tailInter B m ⊆ B m := by
  intro ω hω
  simp only [tailInter, mem_iInter] at hω
  exact hω m le_rfl

/-- If `B n` holds eventually almost surely, the tails `⋂_{n ≥ m} B n` exhaust a set of full measure. -/
lemma measure_compl_iUnion_tailInter {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {B : ℕ → Set Ω}
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ B n) :
    P (⋃ m, tailInter B m)ᶜ = 0 := by
  rw [ae_iff] at hev
  refine measure_mono_null (fun ω hω => ?_) hev
  show ¬ ∀ᶠ n in atTop, ω ∈ B n
  rw [Filter.not_eventually, frequently_atTop]
  intro a
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  exact hω (mem_iUnion.2 ⟨a, mem_iInter.2 fun n => mem_iInter.2 fun hn => hcon n hn⟩)

/-- Joint probability at one level: if `p ≤ P A` with `p > 0`, and `B n` holds eventually almost surely, then for some
single `n` the joint probability `P (A ∩ B n)` is at least `p / 2`. -/
theorem exists_joint_prob_ge {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {A : Set Ω} {p : ℝ} (hp : 0 < p) (hpA : ENNReal.ofReal p ≤ P A)
    {B : ℕ → Set Ω} (hB : ∀ n, MeasurableSet (B n))
    (hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ B n) :
    ∃ n : ℕ, ENNReal.ofReal (p / 2) ≤ P (A ∩ B n) := by
  have hmono : Monotone (fun m => A ∩ tailInter B m) :=
    fun m m' h => inter_subset_inter_right A (tailInter_mono B h)
  have hU : MeasurableSet (⋃ m, tailInter B m) :=
    MeasurableSet.iUnion fun m => measurableSet_tailInter hB m
  have hcompl := measure_compl_iUnion_tailInter P hev
  have hfull : P (A ∩ ⋃ m, tailInter B m) = P A := by
    have hsplit := measure_inter_add_sdiff A hU (μ := P)
    have hdiff : P (A \ ⋃ m, tailInter B m) = 0 :=
      measure_mono_null (fun x hx => hx.2) hcompl
    rw [hdiff, add_zero] at hsplit
    exact hsplit
  have hlim : Tendsto (P ∘ fun m => A ∩ tailInter B m) atTop (𝓝 (P A)) := by
    have h1 := tendsto_measure_iUnion_atTop (μ := P) hmono
    rw [← inter_iUnion, hfull] at h1
    exact h1
  have hlt : ENNReal.ofReal (p / 2) < P A := by
    refine lt_of_lt_of_le ?_ hpA
    exact (ENNReal.ofReal_lt_ofReal_iff hp).2 (by linarith)
  obtain ⟨m, hm⟩ := (hlim.eventually_const_lt hlt).exists
  exact ⟨m, le_trans hm.le (measure_mono (inter_subset_inter_right A (tailInter_subset B m)))⟩

end FirstPassS11i
