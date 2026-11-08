import HarmonicBalls.Steps.Sec11.WeylPathConcatenation
import HarmonicBalls.Steps.Sec11.WeylLocalCurveLength
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-! # Finite prefixes of a summable path concatenation

Successive length-parametrized pieces can be joined without changing the
previous prefix, including when some pieces have zero duration.
-/

namespace HarmonicBalls

open Set Filter
open scoped BigOperators Topology

/-- The duration of the first `n + 1` pieces. -/
noncomputable def pathPrefixDuration (L : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1), L i

/-- The concatenation of the first `n + 1` pieces, in their original time. -/
noncomputable def pathPrefix (L : ℕ → ℝ) (p : ℕ → ℝ → ℂ) : ℕ → ℝ → ℂ
  | 0 => p 0
  | n + 1 => fun t => if t ≤ pathPrefixDuration L n then pathPrefix L p n t
      else p (n + 1) (t - pathPrefixDuration L n)

@[simp] theorem pathPrefixDuration_zero (L : ℕ → ℝ) : pathPrefixDuration L 0 = L 0 := by
  simp [pathPrefixDuration]

@[simp] theorem pathPrefixDuration_succ (L : ℕ → ℝ) (n : ℕ) :
    pathPrefixDuration L (n + 1) = pathPrefixDuration L n + L (n + 1) := by
  simp [pathPrefixDuration, Finset.sum_range_succ]

/-- Each prefix is length-parametrized and ends at the end of its last piece. -/
theorem IsEuclideanLengthMetric.pathPrefix_parametrized
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (L : ℕ → ℝ) (p : ℕ → ℝ → ℂ)
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) :
    ∀ n, IsLengthParametrized D (pathPrefix L p n) (pathPrefixDuration L n) ∧
      pathPrefix L p n (pathPrefixDuration L n) = p n (L n) := by
  intro n
  induction n with
  | zero =>
    constructor
    · simpa [pathPrefix] using hp 0
    · simp [pathPrefix]
  | succ n ih =>
    have hj : pathPrefix L p n (pathPrefixDuration L n) = p (n + 1) 0 :=
      ih.2.trans (hjoin n)
    have hparam := hD.isLengthParametrized_piecewise_concat ih.1 (hp (n + 1)) hj
    constructor
    · simpa only [pathPrefix, pathPrefixDuration_succ] using hparam
    · rw [pathPrefixDuration_succ, pathPrefix]
      by_cases hzero : L (n + 1) = 0
      · simp only [hzero, add_zero, le_refl, ite_true]
        simpa only [hzero] using hj
      · have hpos : 0 < L (n + 1) := lt_of_le_of_ne (hp (n + 1)).1 (Ne.symm hzero)
        simp only [not_le_of_gt (lt_add_of_pos_right _ hpos), ite_false, add_sub_cancel_left]

/-- A longer finite concatenation agrees with its earlier prefix. -/
theorem pathPrefix_eqOn {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ}
    (hL : ∀ n, 0 ≤ L n) {n m : ℕ} (hnm : n ≤ m) :
    EqOn (pathPrefix L p m) (pathPrefix L p n) (Icc 0 (pathPrefixDuration L n)) := by
  have hmono : Monotone (pathPrefixDuration L) := monotone_nat_of_le_succ (fun k => by
    rw [pathPrefixDuration_succ]
    linarith [hL (k + 1)])
  induction hnm with
  | refl => intro t ht; rfl
  | @step m hnm ih =>
    intro t ht
    change (if t ≤ pathPrefixDuration L m then pathPrefix L p m t
      else p (m + 1) (t - pathPrefixDuration L m)) = _
    rw [ite_eq_left (le_trans ht.2 (hmono hnm))]
    exact ih ht

/-- A countable concatenation, with the limiting endpoint set to zero. -/
noncomputable def summablePath (L : ℕ → ℝ) (p : ℕ → ℝ → ℂ) (S : ℝ) (t : ℝ) : ℂ := by
  classical
  exact if t < S then
    if h : ∃ n, t ≤ pathPrefixDuration L n then pathPrefix L p (Nat.find h) t else 0
  else 0

/-- Every finite prefix gives the same value at times it covers, before the endpoint. -/
theorem summablePath_eq_prefix {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S t : ℝ}
    (hL : ∀ n, 0 ≤ L n) (ht : 0 ≤ t) (htS : t < S) {n : ℕ}
    (htn : t ≤ pathPrefixDuration L n) :
    summablePath L p S t = pathPrefix L p n t := by
  classical
  have hex : ∃ n, t ≤ pathPrefixDuration L n := ⟨n, htn⟩
  simp only [summablePath, htS, ite_true, dite_eq_left hex]
  let k := Nat.find hex
  have htk : t ≤ pathPrefixDuration L k := Nat.find_spec hex
  rcases le_total k n with hkn | hnk
  · exact (pathPrefix_eqOn hL hkn ⟨ht, htk⟩).symm
  · exact pathPrefix_eqOn hL hnk ⟨ht, htn⟩

/-- Prefix durations converge to the sum of the nonnegative durations. -/
theorem tendsto_pathPrefixDuration {L : ℕ → ℝ} {S : ℝ} (h : HasSum L S) :
    Tendsto (pathPrefixDuration L) atTop (𝓝 S) := by
  exact h.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)

/-- Any time strictly before the total duration belongs to a finite prefix. -/
theorem exists_pathPrefixDuration_ge {L : ℕ → ℝ} {S t : ℝ}
    (h : HasSum L S) (ht : t < S) : ∃ n, t ≤ pathPrefixDuration L n := by
  have he := (tendsto_pathPrefixDuration h).eventually (Ioi_mem_nhds ht)
  obtain ⟨n, hn⟩ := eventually_atTop.mp he
  exact ⟨n, le_of_lt (hn n le_rfl)⟩

/-- Before the endpoint, the concatenation is one-Lipschitz in the metric. -/
theorem IsEuclideanLengthMetric.summablePath_dist_le_before
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t < S) :
    D (summablePath L p S s) (summablePath L p S t) ≤ t - s := by
  obtain ⟨n, hn⟩ := exists_pathPrefixDuration_ge hsum ht
  have hL : ∀ n, 0 ≤ L n := fun n => (hp n).1
  rw [summablePath_eq_prefix hL hs (lt_of_le_of_lt hst ht) (le_trans hst hn),
    summablePath_eq_prefix hL (le_trans hs hst) ht hn]
  simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using
    hD.dist_le_of_lengthParametrized (hD.pathPrefix_parametrized L p hp hjoin n).1
      ⟨hs, le_trans hst hn⟩ ⟨le_trans hs hst, hn⟩

/-- The endpoint estimate follows from convergence of the piece endpoints. -/
theorem IsEuclideanLengthMetric.summablePath_dist_endpoint_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    {s : ℝ} (hs : 0 ≤ s) (hsS : s < S) :
    D (summablePath L p S s) 0 ≤ S - s := by
  have hL : ∀ n, 0 ≤ L n := fun n => (hp n).1
  have hl : Tendsto (fun n => D (summablePath L p S s) (p n (L n)))
      atTop (𝓝 (D (summablePath L p S s) 0)) :=
    (hD.continuous_pair.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hend)
  have hr : Tendsto (fun n => pathPrefixDuration L n - s) atTop (𝓝 (S - s)) :=
    (tendsto_pathPrefixDuration hsum).sub_const s
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards [(tendsto_pathPrefixDuration hsum).eventually (Ioi_mem_nhds hsS)] with n hn
  have hpref := hD.pathPrefix_parametrized L p hp hjoin n
  have hs' : s ≤ pathPrefixDuration L n := le_of_lt hn
  rw [summablePath_eq_prefix hL hs hsS hs', ← hpref.2]
  simpa only [abs_of_nonneg (sub_nonneg.mpr hs')] using
    hD.dist_le_of_lengthParametrized hpref.1 ⟨hs, hs'⟩ ⟨hpref.1.1, le_rfl⟩

/-- The completed concatenation has metric increments bounded by elapsed time. -/
theorem IsEuclideanLengthMetric.summablePath_dist_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ S) :
    D (summablePath L p S s) (summablePath L p S t) ≤ t - s := by
  by_cases htS : t < S
  · exact hD.summablePath_dist_le_before hp hjoin hsum hs hst htS
  · have ht' : t = S := le_antisymm ht (le_of_not_gt htS)
    subst t
    by_cases hsS : s < S
    · simpa only [summablePath, lt_self_iff_false, ite_false] using
        hD.summablePath_dist_endpoint_le hp hjoin hsum hend hs hsS
    · have hs' : s = S := le_antisymm hst (le_of_not_gt hsS)
      subst s
      simp only [hD.self_eq_zero, sub_self, le_refl]

/-- Every finite prefix duration is at most the total duration. -/
theorem pathPrefixDuration_le_sum {L : ℕ → ℝ} {S : ℝ}
    (hL : ∀ n, 0 ≤ L n) (hsum : HasSum L S) (n : ℕ) :
    pathPrefixDuration L n ≤ S := by
  rw [← hsum.tsum_eq]
  exact hsum.summable.sum_le_tsum _ (fun i _ => hL i)

/-- If a prefix exhausts all time, its endpoint is the appended endpoint. -/
theorem IsEuclideanLengthMetric.pathPrefix_endpoint_eq_zero_of_duration_eq
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (n : ℕ) (hn : pathPrefixDuration L n = S) : p n (L n) = 0 := by
  have hL : ∀ n, 0 ≤ L n := fun n => (hp n).1
  have hmono : Monotone (pathPrefixDuration L) := monotone_nat_of_le_succ (fun k => by
    rw [pathPrefixDuration_succ]; linarith [hL (k + 1)])
  have hl : Tendsto (fun m => D (p n (L n)) (p m (L m))) atTop
      (𝓝 (D (p n (L n)) 0)) :=
    (hD.continuous_pair.tendsto _).comp (tendsto_const_nhds.prodMk_nhds hend)
  have hr : Tendsto (fun m => pathPrefixDuration L m - pathPrefixDuration L n)
      atTop (𝓝 0) := by
    simpa only [hn, sub_self] using (tendsto_pathPrefixDuration hsum).sub_const S
  have hle : D (p n (L n)) 0 ≤ 0 := by
    apply le_of_tendsto_of_tendsto hl hr
    filter_upwards [eventually_ge_atTop n] with m hnm
    have hpn := hD.pathPrefix_parametrized L p hp hjoin n
    have hpm := hD.pathPrefix_parametrized L p hp hjoin m
    have heq := pathPrefix_eqOn (p := p) hL hnm ⟨hpn.1.1, le_rfl⟩
    have hdist := hD.dist_le_of_lengthParametrized hpm.1
      ⟨hpn.1.1, hmono hnm⟩ ⟨hpm.1.1, le_rfl⟩
    rw [heq, hpn.2, hpm.2, abs_of_nonneg (sub_nonneg.mpr (hmono hnm))] at hdist
    exact hdist
  apply hD.eq_of_eq_zero
  have hnneg : 0 ≤ D (p n (L n)) 0 := by
    have htri := hD.triangle (p n (L n)) 0 (p n (L n))
    rw [hD.self_eq_zero, hD.symm 0 (p n (L n))] at htri
    linarith
  exact le_antisymm hle hnneg

/-- The completed path agrees with every finite prefix throughout that prefix,
including a prefix that exhausts the whole duration. -/
theorem IsEuclideanLengthMetric.summablePath_eq_prefix
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (pathPrefixDuration L n)) :
    summablePath L p S t = pathPrefix L p n t := by
  have hL : ∀ n, 0 ≤ L n := fun n => (hp n).1
  have hle := pathPrefixDuration_le_sum hL hsum n
  by_cases htS : t < S
  · exact HarmonicBalls.summablePath_eq_prefix hL ht.1 htS ht.2
  · have ht' : t = S := le_antisymm (le_trans ht.2 hle) (le_of_not_gt htS)
    have hn : pathPrefixDuration L n = S := le_antisymm hle (ht' ▸ ht.2)
    subst t
    rw [← hn, (hD.pathPrefix_parametrized L p hp hjoin n).2,
      hD.pathPrefix_endpoint_eq_zero_of_duration_eq hp hjoin hsum hend n hn]
    simp [summablePath, hn]

/-- The first piece is traced on its entire interval. -/
theorem IsEuclideanLengthMetric.summablePath_eq_first_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc 0 (L 0)) : summablePath L p S t = p 0 t := by
  simpa only [pathPrefixDuration_zero, pathPrefix] using
    hD.summablePath_eq_prefix hp hjoin hsum hend 0 (by simpa only [pathPrefixDuration_zero] using ht)

/-- Each later piece is traced after the preceding prefix, even if it has
zero duration. -/
theorem IsEuclideanLengthMetric.summablePath_eq_succ_piece
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0))
    (n : ℕ) {t : ℝ} (ht : t ∈ Icc 0 (L (n + 1))) :
    summablePath L p S (pathPrefixDuration L n + t) = p (n + 1) t := by
  have hpref := hD.pathPrefix_parametrized L p hp hjoin n
  have hmem : pathPrefixDuration L n + t ∈ Icc 0 (pathPrefixDuration L (n + 1)) := by
    rw [pathPrefixDuration_succ]
    constructor <;> linarith [hpref.1.1, ht.1, ht.2]
  rw [hD.summablePath_eq_prefix hp hjoin hsum hend (n + 1) hmem]
  change (if pathPrefixDuration L n + t ≤ pathPrefixDuration L n then _ else _) = _
  by_cases ht0 : t = 0
  · subst t
    simpa only [add_zero, le_refl, ite_true] using hpref.2.trans (hjoin n)
  · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    simp only [not_le_of_gt (lt_add_of_pos_right _ htpos), ite_false, add_sub_cancel_left]

/-- Shrinking Euclidean balls force the piece endpoints to converge to zero. -/
theorem tendsto_piece_endpoints_of_norm_le {L r : ℕ → ℝ} {p : ℕ → ℝ → ℂ}
    (hL : ∀ n, 0 ≤ L n) (hr : Tendsto r atTop (𝓝 0))
    (hball : ∀ n t, t ∈ Icc 0 (L n) → ‖p n t‖ ≤ r n) :
    Tendsto (fun n => p n (L n)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) (fun n => hball n _ ⟨hL n, le_rfl⟩) hr

/-- The completed concatenation is continuous in the Euclidean topology. -/
theorem IsEuclideanLengthMetric.summablePath_continuousOn
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0)) :
    ContinuousOn (summablePath L p S) (Icc 0 S) := by
  intro t ht
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hopen : IsOpen (Metric.ball (summablePath L p S t) ε) := Metric.isOpen_ball
  obtain ⟨δ, hδ, hball⟩ := (hD.isOpen_iff _).mp hopen _ (Metric.mem_ball_self hε)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxt
  apply hball
  have hbound : D (summablePath L p S t) (summablePath L p S x) ≤ dist x t := by
    rcases le_total t x with htx | hxt'
    · have h := hD.summablePath_dist_le hp hjoin hsum hend ht.1 htx hx.2
      simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr htx)] using h
    · have h := hD.summablePath_dist_le hp hjoin hsum hend hx.1 hxt' ht.2
      rw [hD.symm] at h
      simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxt'), neg_sub] using h
  exact lt_of_le_of_lt hbound hxt

/-- A metric one-Lipschitz curve has length at most its parameter duration. -/
theorem curveLength_le_of_ordered_dist_le {D : ℂ → ℂ → ℝ} {p : ℝ → ℂ} {S : ℝ}
    (h : ∀ s t, 0 ≤ s → s ≤ t → t ≤ S → D (p t) (p s) ≤ t - s) :
    curveLength D p 0 S ≤ ENNReal.ofReal S := by
  unfold curveLength
  apply iSup_le
  intro q
  let u := q.2.1
  have hmono : Monotone u := q.2.2.1
  have hmem : ∀ i, u i ∈ Icc (0 : ℝ) S := q.2.2.2
  calc
    _ ≤ ∑ i ∈ Finset.range q.1, ENNReal.ofReal (u (i + 1) - u i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact ENNReal.ofReal_le_ofReal (h _ _ (hmem i).1 (hmono (Nat.le_succ i)) (hmem (i + 1)).2)
    _ = ENNReal.ofReal (u q.1 - u 0) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sub_nonneg.mpr (hmono (Nat.le_succ i))),
        Finset.sum_range_sub]
    _ ≤ ENNReal.ofReal S := ENNReal.ofReal_le_ofReal (by linarith [(hmem q.1).2, (hmem 0).1])

/-- The completed concatenation has finite original-metric length at most `S`. -/
theorem IsEuclideanLengthMetric.summablePath_curveLength_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hend : Tendsto (fun n => p n (L n)) atTop (𝓝 0)) :
    curveLength D (summablePath L p S) 0 S ≤ ENNReal.ofReal S := by
  apply curveLength_le_of_ordered_dist_le
  intro s t hs hst ht
  rw [hD.symm]
  exact hD.summablePath_dist_le hp hjoin hsum hend hs hst ht

/-- Countably many matching length-parametrized pieces in shrinking Euclidean
balls form a continuous finite-length path ending at zero. -/
theorem IsEuclideanLengthMetric.exists_summable_path_concatenation
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {L r : ℕ → ℝ} {p : ℕ → ℝ → ℂ} {S : ℝ}
    (hp : ∀ n, IsLengthParametrized D (p n) (L n))
    (hjoin : ∀ n, p n (L n) = p (n + 1) 0) (hsum : HasSum L S)
    (hr : Tendsto r atTop (𝓝 0))
    (hball : ∀ n t, t ∈ Icc 0 (L n) → ‖p n t‖ ≤ r n) :
    ∃ P : ℝ → ℂ, 0 ≤ S ∧ P S = 0 ∧
      (∀ t ∈ Icc 0 (L 0), P t = p 0 t) ∧
      (∀ n t, t ∈ Icc 0 (L (n + 1)) →
        P (pathPrefixDuration L n + t) = p (n + 1) t) ∧
      ContinuousOn P (Icc 0 S) ∧
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ S → D (P s) (P t) ≤ t - s) ∧
      curveLength D P 0 S ≤ ENNReal.ofReal S := by
  have hend := tendsto_piece_endpoints_of_norm_le (fun n => (hp n).1) hr hball
  refine ⟨summablePath L p S, HasSum.nonneg (fun n => (hp n).1) hsum, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [summablePath]
  · intro t ht
    exact hD.summablePath_eq_first_piece hp hjoin hsum hend ht
  · intro n t ht
    exact hD.summablePath_eq_succ_piece hp hjoin hsum hend n ht
  · exact hD.summablePath_continuousOn hp hjoin hsum hend
  · intro s t hs hst ht
    exact hD.summablePath_dist_le hp hjoin hsum hend hs hst ht
  · exact hD.summablePath_curveLength_le hp hjoin hsum hend

#print axioms IsEuclideanLengthMetric.exists_summable_path_concatenation
#print axioms IsEuclideanLengthMetric.pathPrefix_parametrized
#print axioms pathPrefix_eqOn
#print axioms IsEuclideanLengthMetric.summablePath_dist_le_before
#print axioms IsEuclideanLengthMetric.summablePath_dist_le
#print axioms IsEuclideanLengthMetric.summablePath_eq_succ_piece
#print axioms IsEuclideanLengthMetric.summablePath_eq_prefix
#print axioms IsEuclideanLengthMetric.summablePath_continuousOn
#print axioms IsEuclideanLengthMetric.summablePath_curveLength_le

end HarmonicBalls
