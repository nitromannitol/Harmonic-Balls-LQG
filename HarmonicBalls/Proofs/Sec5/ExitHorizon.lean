import HarmonicBalls.Proofs.Sec5.ClusterMeasurability

/-! # Measurable horizons for increasing open-set families -/

namespace HarmonicBalls

open MeasureTheory Metric Set ProbabilityTheory TopologicalSpace
open scoped ENNReal

/-- The positive times `1 / (n + 1)` form a sequence tending to zero. -/
noncomputable def reciprocalTime (n : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨1 / ((n : ℝ) + 1), by change 0 < 1 / ((n : ℝ) + 1); positivity⟩

/-- The measurable countable test that all sets at a given time stay in a
closed ball. For open sets, this also controls their closures. -/
def denseSequenceBallTest {ι : Type*} (r : ℝ) (F : ι → Set.Ioi (0 : ℝ) → Set ℂ)
    (n : ℕ) : Prop :=
  ∀ i m, denseSeq ℂ m ∈ F i (reciprocalTime n) →
    denseSeq ℂ m ∈ closedBall (0 : ℂ) r

/-- The largest tested reciprocal time at which a countable family is
contained in the closed ball, measured using the countable dense sequence. -/
noncomputable def denseSequenceBallHorizon {ι : Type*} (r : ℝ)
    (F : ι → Set.Ioi (0 : ℝ) → Set ℂ) : ℝ≥0∞ := by
  classical
  exact ⨆ n, if denseSequenceBallTest r F n then
    ENNReal.ofReal (reciprocalTime n) else 0

/-- The countable ball test is measurable in the pointwise set structure. -/
theorem measurable_denseSequenceBallTest {ι : Type*} [Countable ι] (r : ℝ) (n : ℕ) :
    Measurable (fun F : ι → Set.Ioi (0 : ℝ) → Set ℂ => denseSequenceBallTest r F n) := by
  unfold denseSequenceBallTest
  apply Measurable.forall
  intro i
  apply Measurable.forall
  intro m
  have heval : Measurable (fun F : ι → Set.Ioi (0 : ℝ) → Set ℂ =>
      denseSeq ℂ m ∈ F i (reciprocalTime n)) := by
    have hF : Measurable (fun F : ι → Set.Ioi (0 : ℝ) → Set ℂ =>
        F i (reciprocalTime n)) :=
      (measurable_pi_apply (reciprocalTime n)).comp (measurable_pi_apply i)
    exact (measurable_pi_apply (denseSeq ℂ m)).comp hF
  exact heval.imp measurable_const

/-- The horizon is measurable for any countable family of set-valued paths. -/
theorem measurable_denseSequenceBallHorizon {ι : Type*} [Countable ι] (r : ℝ) :
    Measurable (denseSequenceBallHorizon (ι := ι) r) := by
  classical
  unfold denseSequenceBallHorizon
  apply Measurable.iSup
  intro n
  exact Measurable.ite (measurable_denseSequenceBallTest (ι := ι) r n).setOf measurable_const measurable_const

/-- A successful dense-sequence test contains all closures when the sets
are open. -/
theorem closure_subset_closedBall_of_denseSequenceBallTest {ι : Type*} {r : ℝ}
    {F : ι → Set.Ioi (0 : ℝ) → Set ℂ} {n : ℕ}
    (h : denseSequenceBallTest r F n) (hopen : ∀ i, IsOpen (F i (reciprocalTime n)))
    (i : ι) : closure (F i (reciprocalTime n)) ⊆ closedBall (0 : ℂ) r := by
  rw [closure_eq_closure_inter_denseSeq (hopen i)]
  apply closure_minimal _ isClosed_closedBall
  rintro x ⟨hx, m, rfl⟩
  exact h i m hx

/-- Every successful test is bounded by the measurable horizon. -/
theorem ofReal_reciprocalTime_le_denseSequenceBallHorizon {ι : Type*} {r : ℝ}
    {F : ι → Set.Ioi (0 : ℝ) → Set ℂ} {n : ℕ} (h : denseSequenceBallTest r F n) :
    ENNReal.ofReal (reciprocalTime n) ≤ denseSequenceBallHorizon r F := by
  classical
  exact le_iSup_of_le n (by simp [h])

/-- A successful test gives a strictly positive horizon. -/
theorem denseSequenceBallHorizon_pos {ι : Type*} {r : ℝ}
    {F : ι → Set.Ioi (0 : ℝ) → Set ℂ} {n : ℕ} (h : denseSequenceBallTest r F n) :
    0 < denseSequenceBallHorizon r F := by
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (reciprocalTime n).property)
    (ofReal_reciprocalTime_le_denseSequenceBallHorizon h)

/-- Increasing open families remain inside the closed ball strictly before
this horizon. -/
theorem closure_subset_closedBall_of_lt_denseSequenceBallHorizon {ι : Type*} {r : ℝ}
    {F : ι → Set.Ioi (0 : ℝ) → Set ℂ}
    (hopen : ∀ i t, IsOpen (F i t)) (hmono : ∀ i, Monotone (F i))
    {t : Set.Ioi (0 : ℝ)} (ht : ENNReal.ofReal t < denseSequenceBallHorizon r F)
    (i : ι) : closure (F i t) ⊆ closedBall (0 : ℂ) r := by
  classical
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp ht
  by_cases hs : denseSequenceBallTest r F n
  · have hle : t ≤ reciprocalTime n := by
      have hlt : ENNReal.ofReal (t : ℝ) < ENNReal.ofReal (reciprocalTime n) := by
        simpa [hs] using hn
      exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (reciprocalTime n).property).mp hlt)
    exact (closure_mono (hmono i hle)).trans
      (closure_subset_closedBall_of_denseSequenceBallTest hs (fun i => hopen i _) i)
  · simp [hs] at hn

/-- Every horizon is finite, in fact at most one. -/
theorem denseSequenceBallHorizon_le_one {ι : Type*} (r : ℝ)
    (F : ι → Set.Ioi (0 : ℝ) → Set ℂ) : denseSequenceBallHorizon r F ≤ 1 := by
  classical
  apply iSup_le
  intro n
  by_cases h : denseSequenceBallTest r F n
  · simp only [h, ↓reduceIte, ENNReal.ofReal_le_one]
    change 1 / ((n : ℝ) + 1) ≤ 1
    exact (div_le_one (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  · simp [h]

/-- The finite real-valued version of the countable ball horizon. -/
noncomputable def realDenseSequenceBallHorizon {ι : Type*} (r : ℝ)
    (F : ι → Set.Ioi (0 : ℝ) → Set ℂ) : ℝ :=
  (denseSequenceBallHorizon r F).toReal

/-- The real-valued horizon is measurable. -/
theorem measurable_realDenseSequenceBallHorizon {ι : Type*} [Countable ι] (r : ℝ) :
    Measurable (realDenseSequenceBallHorizon (ι := ι) r) :=
  (measurable_denseSequenceBallHorizon r).ennreal_toReal

/-- If a whole increasing family is contained in the ball at one positive
 time, the horizon selected by the countable tests is positive. -/
theorem realDenseSequenceBallHorizon_pos_of_subset {ι : Type*} {r : ℝ}
    {F : ι → Set.Ioi (0 : ℝ) → Set ℂ}
    (hmono : ∀ i, Monotone (F i)) {s : Set.Ioi (0 : ℝ)}
    (hs : ∀ i, F i s ⊆ closedBall (0 : ℂ) r) :
    0 < realDenseSequenceBallHorizon r F := by
  have hspos : 0 < (s : ℝ) := s.property
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hspos
  have ht : reciprocalTime n ≤ s := le_of_lt hn
  have htest : denseSequenceBallTest r F n := by
    intro i m hm
    exact hs i (hmono i ht hm)
  apply ENNReal.toReal_pos (ne_of_gt (denseSequenceBallHorizon_pos htest))
  exact ne_top_of_le_ne_top (by simp) (denseSequenceBallHorizon_le_one r F)

/-- The real-valued horizon controls all closures at earlier positive times. -/
theorem closure_subset_closedBall_of_lt_realDenseSequenceBallHorizon {ι : Type*} {r : ℝ}
    {F : ι → Set.Ioi (0 : ℝ) → Set ℂ}
    (hopen : ∀ i t, IsOpen (F i t)) (hmono : ∀ i, Monotone (F i))
    {t : Set.Ioi (0 : ℝ)} (ht : (t : ℝ) < realDenseSequenceBallHorizon r F)
    (i : ι) : closure (F i t) ⊆ closedBall (0 : ℂ) r := by
  apply closure_subset_closedBall_of_lt_denseSequenceBallHorizon hopen hmono ?_ i
  have hfinite : denseSequenceBallHorizon r F ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (denseSequenceBallHorizon_le_one r F)
  rw [← ENNReal.ofReal_toReal hfinite]
  have htpos : 0 < (t : ℝ) := t.property
  have hrealpos : 0 < (denseSequenceBallHorizon r F).toReal := lt_trans htpos ht
  exact (ENNReal.ofReal_lt_ofReal_iff hrealpos).mpr ht

/-- A countable family controls every centre if each set is contained in the
closure of the union over that family. This separates the measurable-horizon
construction from the required continuity in the centre. -/
theorem closure_subset_closedBall_of_countable_centres {ι J : Type*} {r : ℝ}
    {F : J → Set.Ioi (0 : ℝ) → Set ℂ} (e : ι → J)
    (hopen : ∀ i t, IsOpen (F (e i) t)) (hmono : ∀ i, Monotone (F (e i)))
    (hcover : ∀ j t, F j t ⊆ closure (⋃ i, F (e i) t))
    {t : Set.Ioi (0 : ℝ)}
    (ht : (t : ℝ) < realDenseSequenceBallHorizon r (fun i => F (e i)))
    (j : J) : closure (F j t) ⊆ closedBall (0 : ℂ) r := by
  have hsub : (⋃ i, F (e i) t) ⊆ closedBall (0 : ℂ) r := by
    apply iUnion_subset
    intro i
    exact subset_closure.trans
      (closure_subset_closedBall_of_lt_realDenseSequenceBallHorizon hopen hmono ht i)
  exact closure_minimal ((hcover j t).trans (closure_minimal hsub isClosed_closedBall))
    isClosed_closedBall

/-- Restricting a set-valued family to any prescribed collection of centres
is measurable for the pointwise measurable structure. -/
theorem measurable_restrictCentres {ι J : Type*} (e : ι → J) :
    Measurable (fun F : J → Set.Ioi (0 : ℝ) → Set ℂ => fun i => F (e i)) := by
  apply Measurable.of_eval
  intro i
  exact measurable_pi_apply (e i)

/-- Joint laws determine the law of the horizon tested on a countable set of
centres. -/
theorem identDistrib_countableCentresHorizon {Ω Ω' ι J : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Countable ι] {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → J → Set.Ioi (0 : ℝ) → Set ℂ}
    {Y : Ω' → J → Set.Ioi (0 : ℝ) → Set ℂ}
    (r : ℝ) (e : ι → J) (h : IdentDistrib X Y P Q) :
    IdentDistrib (fun ω => realDenseSequenceBallHorizon r (fun i => X ω (e i)))
      (fun ω => realDenseSequenceBallHorizon r (fun i => Y ω (e i))) P Q :=
  h.comp ((measurable_realDenseSequenceBallHorizon (ι := ι) r).comp
    (measurable_restrictCentres e))

/-- Equal family laws give equal laws for the real horizons. -/
theorem identDistrib_realDenseSequenceBallHorizon {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Countable ι] {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → ι → Set.Ioi (0 : ℝ) → Set ℂ}
    {Y : Ω' → ι → Set.Ioi (0 : ℝ) → Set ℂ}
    (r : ℝ) (h : IdentDistrib X Y P Q) :
    IdentDistrib (fun ω => realDenseSequenceBallHorizon r (X ω))
      (fun ω => realDenseSequenceBallHorizon r (Y ω)) P Q :=
  h.comp (measurable_realDenseSequenceBallHorizon (ι := ι) r)

/-- Identically distributed families have identically distributed horizons. -/
theorem identDistrib_denseSequenceBallHorizon {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [Countable ι] {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → ι → Set.Ioi (0 : ℝ) → Set ℂ}
    {Y : Ω' → ι → Set.Ioi (0 : ℝ) → Set ℂ}
    (r : ℝ) (h : IdentDistrib X Y P Q) :
    IdentDistrib (fun ω => denseSequenceBallHorizon r (X ω))
      (fun ω => denseSequenceBallHorizon r (Y ω)) P Q :=
  h.comp (measurable_denseSequenceBallHorizon (ι := ι) r)

end HarmonicBalls
