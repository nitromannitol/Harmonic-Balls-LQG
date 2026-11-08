import HarmonicBalls.Proofs.Metric.SummablePathConcatenation
import Mathlib.Order.Interval.Set.Union
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-! # Original arclength and weighted length of summable concatenations -/

namespace HarmonicBalls

open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal Function

/-- Length is monotone under inclusion of parameter intervals. -/
theorem curveLength_mono_interval {D : ℂ → ℂ → ℝ} {p : ℝ → ℂ}
    {a b c d : ℝ} (hac : c ≤ a) (hbd : b ≤ d) :
    curveLength D p a b ≤ curveLength D p c d := by
  unfold curveLength
  apply iSup_le
  intro q
  let v : {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc c d} :=
    ⟨q.2.1, q.2.2.1, fun i => ⟨hac.trans (q.2.2.2 i).1, (q.2.2.2 i).2.trans hbd⟩⟩
  exact le_iSup (fun x : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc c d} =>
    ∑ i ∈ Finset.range x.1, ENNReal.ofReal (D (p (x.2.1 (i + 1))) (p (x.2.1 i)))) ⟨q.1, v⟩

/-- The completed concatenation preserves the original arclength parametrization. -/
theorem IsEuclideanLengthMetric.summablePath_parametrized
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0)) :
    IsLengthParametrized D (summablePath L p S) S := by
  have hL : ∀ n, 0 ≤ L n := fun n => (hp n).1
  have hS : 0 ≤ S := HasSum.nonneg hL hsum
  refine ⟨hS, hD.summablePath_continuousOn hp hjoin hsum hend, ?_⟩
  intro a b ha hab hb
  apply le_antisymm
  · unfold curveLength
    apply iSup_le
    intro q
    have hmono := q.2.2.1
    have hmem := q.2.2.2
    calc
      _ ≤ ∑ i ∈ Finset.range q.1, ENNReal.ofReal (q.2.1 (i + 1) - q.2.1 i) := by
        apply Finset.sum_le_sum
        intro i hi
        apply ENNReal.ofReal_le_ofReal
        rw [hD.symm]
        exact hD.summablePath_dist_le hp hjoin hsum hend
          (ha.trans (hmem i).1) (hmono (Nat.le_succ i)) ((hmem (i + 1)).2.trans hb)
      _ = ENNReal.ofReal (q.2.1 q.1 - q.2.1 0) := by
        rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hmono (Nat.le_succ i))),
          Finset.sum_range_sub]
      _ ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal (by linarith [(hmem q.1).2, (hmem 0).1])
  · by_cases haS : a < S
    · have hlim : Tendsto (fun n => ENNReal.ofReal (min b (pathPrefixDuration L n) - a))
          atTop (𝓝 (ENNReal.ofReal (b - a))) := by
        have hmin : Tendsto (fun n => min b (pathPrefixDuration L n) - a) atTop
            (𝓝 (min b S - a)) :=
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => b) atTop (𝓝 b)).min
            (tendsto_pathPrefixDuration hsum)).sub_const a
        simpa only [min_eq_left hb] using (ENNReal.tendsto_ofReal hmin)
      apply le_of_tendsto' hlim
      intro n
      by_cases han : a ≤ pathPrefixDuration L n
      · have hmin : a ≤ min b (pathPrefixDuration L n) := le_min hab han
        have hpre := (hD.pathPrefix_parametrized L p hp hjoin n).1
        have heq : curveLength D (summablePath L p S) a (min b (pathPrefixDuration L n)) =
            curveLength D (pathPrefix L p n) a (min b (pathPrefixDuration L n)) := by
          apply curveLength_eq_of_eqOn
          intro t ht
          apply hD.summablePath_eq_prefix hp hjoin hsum hend n
          exact ⟨ha.trans ht.1, ht.2.trans (min_le_right _ _)⟩
        calc
          _ = curveLength D (pathPrefix L p n) a (min b (pathPrefixDuration L n)) :=
            (hpre.2.2 a _ ha hmin (min_le_right _ _)).symm
          _ = curveLength D (summablePath L p S) a (min b (pathPrefixDuration L n)) := heq.symm
          _ ≤ _ := curveLength_mono_interval le_rfl (min_le_left _ _)
      · have : min b (pathPrefixDuration L n) - a ≤ 0 := by linarith [min_le_right b (pathPrefixDuration L n)]
        simp [ENNReal.ofReal_eq_zero.mpr this]
    · have : b = a := le_antisymm (hb.trans (le_of_not_gt haS)) hab
      subst b
      simp

/-- Shrinking balls yield an original-arclength parametrization. -/
theorem IsEuclideanLengthMetric.summablePath_parametrized_of_norm_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L r : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hr : Tendsto r atTop (𝓝 0))
    (hball : ∀ n t, t ∈ Icc 0 (L n) → ‖p n t‖ ≤ r n) :
    IsLengthParametrized D (summablePath L p S) S :=
  hD.summablePath_parametrized hp hjoin hsum
    (tendsto_piece_endpoints_of_norm_le (fun n => (hp n).1) hr hball)

/-- Starting time of the `n`th piece. -/
noncomputable def pathPieceStart (L : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, L i

@[simp] theorem pathPieceStart_zero (L : ℕ → ℝ) : pathPieceStart L 0 = 0 := by
  simp [pathPieceStart]

@[simp] theorem pathPieceStart_succ (L : ℕ → ℝ) (n : ℕ) :
    pathPieceStart L (n + 1) = pathPieceStart L n + L n := by
  simp [pathPieceStart, Finset.sum_range_succ]

theorem pathPieceStart_mono {L : ℕ → ℝ} (hL : ∀ n, 0 ≤ L n) :
    Monotone (pathPieceStart L) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [pathPieceStart_succ]
  linarith [hL n]

/-- Consecutive half-open piece intervals cover all times before the limit. -/
theorem iUnion_piece_intervals {L : ℕ → ℝ} {S : ℝ}
    (hL : ∀ n, 0 ≤ L n) (hsum : HasSum L S) :
    (⋃ n, Ico (pathPieceStart L n) (pathPieceStart L (n + 1))) = Ico 0 S := by
  have hm := pathPieceStart_mono hL
  have hle : ∀ n, pathPieceStart L n ≤ S := by
    intro n
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_le_tsum _ (fun i _ => hL i)
  apply Subset.antisymm
  · refine iUnion_subset fun n t ht => ⟨?_, lt_of_lt_of_le ht.2 (hle (n + 1))⟩
    exact (by simpa using hm (Nat.zero_le n) : 0 ≤ pathPieceStart L n) |>.trans ht.1
  · intro t ht
    have he := (tendsto_pathPrefixDuration hsum).eventually (Ioi_mem_nhds ht.2)
    obtain ⟨n, hn⟩ := eventually_atTop.mp he
    have hn' : t < pathPieceStart L (n + 1) := hn n le_rfl
    obtain ⟨k, hk, hkt⟩ := mem_iUnion₂.mp (Ico_subset_biUnion_Ico (n + 1) (pathPieceStart L) (by simpa using (show t ∈ Ico 0 (pathPieceStart L (n+1)) from ⟨ht.1, hn'⟩)))
    exact mem_iUnion.mpr ⟨k, hkt⟩

/-- On each piece, the concatenation uses that piece's original parameter. -/
theorem IsEuclideanLengthMetric.summablePath_eq_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (L n)) :
    summablePath L p S (pathPieceStart L n + t) = p n t := by
  cases n with
  | zero => simpa using hD.summablePath_eq_first_piece hp hjoin hsum hend ht
  | succ n =>
    have h := hD.summablePath_eq_succ_piece hp hjoin hsum hend n ht
    simpa [pathPieceStart, pathPrefixDuration] using h

/-- Translation preserves nonnegative integrals over closed real intervals. -/
theorem lintegral_translate_Icc (f : ℝ → ℝ≥0∞) (a b c : ℝ) :
    (∫⁻ t in Icc a b, f (c + t)) = ∫⁻ t in Icc (c + a) (c + b), f t := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) c).setLIntegral_comp_emb
    (MeasurableEquiv.addLeft c).measurableEmbedding f (Icc a b)
  simpa only [Set.image_const_add_Icc] using h

/-- Nonnegative weighted length is the sum of the lengths of the pieces. -/
theorem IsEuclideanLengthMetric.lintegral_summablePath
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (F : ℂ → ℝ≥0∞) :
    (∫⁻ t in Icc 0 S, F (summablePath L p S t)) =
      ∑' n, ∫⁻ t in Icc 0 (L n), F (p n t) := by
  have hL : ∀ n, 0 ≤ L n := fun n => (hp n).1
  have hm := pathPieceStart_mono hL
  let A := fun n => Ico (pathPieceStart L n) (pathPieceStart L (n + 1))
  have hd : Pairwise (Disjoint on A) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hji
    · apply Set.disjoint_left.mpr
      intro t hti htj
      have hle := hm (Nat.succ_le_of_lt hij)
      exact (not_lt_of_ge (hle.trans htj.1)) hti.2
    · apply Disjoint.symm
      apply Set.disjoint_left.mpr
      intro t htj hti
      have hle := hm (Nat.succ_le_of_lt hji)
      exact (not_lt_of_ge (hle.trans hti.1)) htj.2
  calc
    _ = ∫⁻ t in Ico 0 S, F (summablePath L p S t) := by
      rw [restrict_Ico_eq_restrict_Icc]
    _ = ∫⁻ t in ⋃ n, A n, F (summablePath L p S t) := by
      rw [iUnion_piece_intervals hL hsum]
    _ = ∑' n, ∫⁻ t in A n, F (summablePath L p S t) :=
      lintegral_iUnion (fun _ => measurableSet_Ico) hd _
    _ = ∑' n, ∫⁻ t in Icc 0 (L n), F (p n t) := by
      apply tsum_congr
      intro n
      change (∫⁻ t in Ico (pathPieceStart L n) (pathPieceStart L (n + 1)),
        F (summablePath L p S t)) = _
      rw [restrict_Ico_eq_restrict_Icc, pathPieceStart_succ]
      have htrans := lintegral_translate_Icc (fun t => F (summablePath L p S t)) 0 (L n) (pathPieceStart L n)
      simp only [add_zero] at htrans
      rw [← htrans]
      apply setLIntegral_congr_fun measurableSet_Icc
      intro t ht
      change F (summablePath L p S (pathPieceStart L n + t)) = F (p n t)
      rw [hD.summablePath_eq_piece hp hjoin hsum hend n ht]

/-- The weighted-integral identity under the shrinking-ball hypotheses. -/
theorem IsEuclideanLengthMetric.lintegral_summablePath_of_norm_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L r : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hr : Tendsto r atTop (𝓝 0))
    (hball : ∀ n t, t ∈ Icc 0 (L n) → ‖p n t‖ ≤ r n)
    (F : ℂ → ℝ≥0∞) :
    (∫⁻ t in Icc 0 S, F (summablePath L p S t)) =
      ∑' n, ∫⁻ t in Icc 0 (L n), F (p n t) :=
  hD.lintegral_summablePath hp hjoin hsum
    (tendsto_piece_endpoints_of_norm_le (fun n => (hp n).1) hr hball) F

#print axioms IsEuclideanLengthMetric.summablePath_parametrized_of_norm_le
#print axioms IsEuclideanLengthMetric.lintegral_summablePath_of_norm_le

end HarmonicBalls
