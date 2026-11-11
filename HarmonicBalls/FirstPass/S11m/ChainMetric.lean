import HarmonicBalls.Steps.Sec11.LocalPathLength
import HarmonicBalls.Steps.Sec11.InternalMetricPaths
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.PinchDistancePositivity
import HarmonicBalls.Steps.Sec11.PinchInequalities
import HarmonicBalls.FirstPass.S11h.SetDistPos

/-!
# Countable recovery of internal metrics by permitted chains (route Step 3.4)

Deterministic part of Step 3.4 of the written proof.

Let `D` be a Euclidean length metric (`IsEuclideanLengthMetric D`), `O` open, `Q` a countable set with `Q ⊆ Oᶜ` and
`Oᶜ ⊆ closure Q` (the set `𝒟_{V∖O}` of the route, with `V = ℂ`), and `S` a set with `O ⊆ closure S` (the vertex set).
The clearance `r_O(v) = inf_{q ∈ Q} D(v, q)`; an edge `v → w` is permitted when `4 D(v, w) < min {r_O(v), r_O(w)}`, with
cost `D(v, w)`. The chain formula `chainDistance S D Q x y` is the infimum of the costs of finite admissible chains from
`x` to `y`. Theorem `chainDistance_eq_internalMetric`: for `x ∈ O`, it equals the internal metric `D(x, y; O)`.

Both inequalities are proved from the route: a permitted edge has an almost minimizing path which stays in `O`, since its
length is below the clearance (chain ≥ internal metric); a path in `O` has compact image, so the clearance is bounded
below along it, and a fine uniform partition with dense vertices gives a permitted chain of cost at most its length
plus `ε` (chain ≤ internal metric).
-/

namespace HarmonicBalls.S11m

open Set Metric Topology unitInterval Filter
open scoped ENNReal

variable {D : ℂ → ℂ → ℝ}

/-- The clearance `r_O(v) = inf_{q ∈ Q} D(v, q)` of a point `v` to a set `Q` (route Step 3.4, `r_O`). -/
noncomputable def clearance (D : ℂ → ℂ → ℝ) (Q : Set ℂ) (v : ℂ) : ℝ≥0∞ :=
  ⨅ q ∈ Q, ENNReal.ofReal (D v q)

/-- The edge `v → w` is permitted when `4 D(v, w) < min {r(v), r(w)}` (route Step 3.4). -/
def PermittedEdge (D : ℂ → ℂ → ℝ) (Q : Set ℂ) (v w : ℂ) : Prop :=
  4 * ENNReal.ofReal (D v w) < min (clearance D Q v) (clearance D Q w)

/-- `v : ℕ → ℂ` is an admissible chain of length `n` from `x` to `y`: its vertices `v 0, …, v n` lie in `S ∪ {x, y}`,
`v 0 = x`, `v n = y`, and every edge `v i → v (i+1)` (`i < n`) is permitted. -/
def AdmissibleChain (S : Set ℂ) (D : ℂ → ℂ → ℝ) (Q : Set ℂ) (x y : ℂ) (n : ℕ) (v : ℕ → ℂ) : Prop :=
  v 0 = x ∧ v n = y ∧ (∀ i ≤ n, v i ∈ S ∪ {x, y}) ∧ ∀ i < n, PermittedEdge D Q (v i) (v (i + 1))

/-- The chain formula: the infimum of the costs `∑ D(v i, v (i+1))` over admissible chains from `x` to `y`
(route Step 3.4). It is defined for every function `D`; no length-metric property is tested. -/
noncomputable def chainDistance (S : Set ℂ) (D : ℂ → ℂ → ℝ) (Q : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (v : ℕ → ℂ) (_ : AdmissibleChain S D Q x y n v),
    ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))

theorem isEuclideanLengthMetric_nonneg (hD : IsEuclideanLengthMetric D) (x y : ℂ) : 0 ≤ D x y := by
  have ht := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at ht
  linarith

/-- If `z` lies in the closure of `Q`, then `D(v, ·)` takes values below `D(v, z) + ε` on `Q`. -/
theorem exists_lt_add_of_mem_closure (hD : IsEuclideanLengthMetric D) {Q : Set ℂ} {v z : ℂ}
    (hz : z ∈ closure Q) {ε : ℝ} (hε : 0 < ε) : ∃ q ∈ Q, D v q < D v z + ε := by
  have hc : Continuous (fun q : ℂ => D v q) :=
    (continuous_uncurry_of_isEuclideanLengthMetric hD).comp (continuous_const.prodMk continuous_id)
  have hev : ∀ᶠ q in 𝓝 z, D v q < D v z + ε :=
    hc.continuousAt.eventually_lt continuousAt_const (lt_add_of_pos_right _ hε)
  obtain ⟨q, hq, hqQ⟩ := mem_closure_iff_nhds.mp hz _ hev
  exact ⟨q, hqQ, hq⟩

/-- The clearance is at most the distance to any point outside `O`, by density of `Q` in `Oᶜ`. -/
theorem clearance_le_of_not_mem (hD : IsEuclideanLengthMetric D) {O Q : Set ℂ} (hQd : Oᶜ ⊆ closure Q)
    {v z : ℂ} (hz : z ∉ O) : clearance D Q v ≤ ENNReal.ofReal (D v z) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨q, hq, hlt⟩ :=
    exists_lt_add_of_mem_closure hD (hQd hz) (ε := (ε : ℝ)) (by exact_mod_cast hε)
  calc clearance D Q v ≤ ENNReal.ofReal (D v q) := iInf₂_le q hq
    _ ≤ ENNReal.ofReal (D v z + ε) := ENNReal.ofReal_le_ofReal hlt.le
    _ = ENNReal.ofReal (D v z) + ε := by
        rw [ENNReal.ofReal_add (isEuclideanLengthMetric_nonneg hD v z) (by positivity), ENNReal.ofReal_coe_nnreal]

/-- A point of positive clearance lies in `O`. -/
theorem mem_of_clearance_pos (hD : IsEuclideanLengthMetric D) {O Q : Set ℂ} (hQd : Oᶜ ⊆ closure Q)
    {v : ℂ} (hv : 0 < clearance D Q v) : v ∈ O := by
  by_contra hvO
  have h := clearance_le_of_not_mem (v := v) hD hQd hvO
  rw [hD.self_eq_zero, ENNReal.ofReal_zero] at h
  exact absurd hv (not_lt.mpr h)

theorem PermittedEdge.clearance_pos_left {Q : Set ℂ} {v w : ℂ} (h : PermittedEdge D Q v w) :
    0 < clearance D Q v := by
  have h1 : 0 < min (clearance D Q v) (clearance D Q w) := lt_of_le_of_lt (by positivity) h
  exact (lt_min_iff.mp h1).1

theorem PermittedEdge.lt_clearance_left {Q : Set ℂ} {v w : ℂ} (h : PermittedEdge D Q v w) :
    ENNReal.ofReal (D v w) < clearance D Q v := by
  have h1 : ENNReal.ofReal (D v w) ≤ 4 * ENNReal.ofReal (D v w) :=
    le_mul_of_one_le_left (by positivity) (by norm_num)
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h (min_le_left _ _))

/-- A permitted edge is at most `η` more expensive than the internal metric on `O` (route Step 3.4, "almost
minimizing paths for permitted edges stay in `O`"). -/
theorem internalMetric_le_of_permitted (hD : IsEuclideanLengthMetric D) {O Q : Set ℂ}
    (hQd : Oᶜ ⊆ closure Q) {v w : ℂ} (hperm : PermittedEdge D Q v w) {η : ℝ≥0∞} (hη : 0 < η) :
    internalMetric D O v w ≤ ENNReal.ofReal (D v w) + η := by
  have ha : ENNReal.ofReal (D v w) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hr : ENNReal.ofReal (D v w) < clearance D Q v := hperm.lt_clearance_left
  obtain ⟨c, hc1, hc2⟩ := exists_between
    (lt_min (ENNReal.lt_add_right ha hη.ne') hr : ENNReal.ofReal (D v w) < min (ENNReal.ofReal (D v w) + η)
      (clearance D Q v))
  have hcr : c < clearance D Q v := lt_of_lt_of_le hc2 (min_le_right _ _)
  have h1 : internalMetric D univ v w < c := by
    rw [← hD.ofReal_eq_internalMetric v w]
    exact hc1
  obtain ⟨P, hP⟩ := iInf_lt_iff.mp h1
  obtain ⟨-, hPc⟩ := iInf_lt_iff.mp hP
  have hPO : ∀ t, P t ∈ O := by
    intro t
    by_contra htO
    have h2 : clearance D Q v ≤ ENNReal.ofReal (D v (P t)) := clearance_le_of_not_mem hD hQd htO
    let q : Path v (P t) := (P.subpath 0 t).cast P.source.symm rfl
    have h3 : ENNReal.ofReal (D v (P t)) ≤ pathLength D q := by
      rw [hD.ofReal_eq_internalMetric v (P t)]
      exact iInf₂_le q (fun _ => mem_univ _)
    have h4 : pathLength D q ≤ pathLength D P := pathLength_subpath_le D P 0 t (Subtype.coe_le_coe.mp (by simpa using t.2.1))
    have h5 : clearance D Q v ≤ pathLength D P := h2.trans (h3.trans h4)
    exact lt_irrefl _ (lt_of_le_of_lt h5 (lt_trans hPc hcr))
  calc internalMetric D O v w ≤ pathLength D P := iInf₂_le P hPO
    _ ≤ c := hPc.le
    _ ≤ ENNReal.ofReal (D v w) + η := hc2.le.trans (min_le_left _ _)

/-- Along an admissible-type chain of permitted edges, the internal metric is at most the cost plus `n η`. -/
theorem internalMetric_chain_le (hD : IsEuclideanLengthMetric D) {O Q : Set ℂ} (hO : IsOpen O)
    (hQd : Oᶜ ⊆ closure Q) {x : ℂ} (hx : x ∈ O) (v : ℕ → ℂ) (hv0 : v 0 = x) (η : ℝ) (hη : 0 < η) (n : ℕ) :
    (∀ i < n, PermittedEdge D Q (v i) (v (i + 1))) →
      internalMetric D O x (v n) ≤
        ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) + ENNReal.ofReal (n * η) := by
  induction n with
  | zero =>
    intro _
    rw [hv0, hD.internalMetric_self_of_mem_open (isEuclideanLengthMetric_nonneg hD) hO hx]
    simp
  | succ n ih =>
    intro hperm
    have hIH := ih (fun i hi => hperm i (Nat.lt_succ_of_lt hi))
    have hedge := internalMetric_le_of_permitted hD hQd (hperm n (Nat.lt_succ_self n))
      (η := ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
    have htri := hD.internalMetric_triangle O x (v n) (v (n + 1))
    have hexp : ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * η) = ENNReal.ofReal (n * η) + ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_add (by positivity) hη.le]
      congr 1
      push_cast
      ring
    calc internalMetric D O x (v (n + 1))
        ≤ internalMetric D O x (v n) + internalMetric D O (v n) (v (n + 1)) := htri
      _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) + ENNReal.ofReal (n * η))
          + (ENNReal.ofReal (D (v n) (v (n + 1))) + ENNReal.ofReal η) := add_le_add hIH hedge
      _ = ∑ i ∈ Finset.range (n + 1), ENNReal.ofReal (D (v i) (v (i + 1)))
          + ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * η) := by
        rw [hexp, Finset.sum_range_succ]
        ring

/-- Lower bound of the chain formula: every admissible chain costs at least the internal metric (route Step 3.4,
"for one inequality, sufficiently short almost minimizing paths for permitted edges stay in `O`"). -/
theorem internalMetric_le_chainDistance (hD : IsEuclideanLengthMetric D) {O S Q : Set ℂ} (hO : IsOpen O)
    (hQd : Oᶜ ⊆ closure Q) {x y : ℂ} (hx : x ∈ O) :
    internalMetric D O x y ≤ chainDistance S D Q x y := by
  refine le_iInf fun n => le_iInf fun v => le_iInf fun hadm => ?_
  obtain ⟨h0, hn, -, hperm⟩ := hadm
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hη : 0 < (ε : ℝ) / ((n : ℝ) + 1) := by positivity
  have key := internalMetric_chain_le hD hO hQd hx v h0 _ hη n hperm
  rw [hn] at key
  have hbound : ENNReal.ofReal (n * ((ε : ℝ) / ((n : ℝ) + 1))) ≤ ENNReal.ofReal ε := by
    apply ENNReal.ofReal_le_ofReal
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  calc internalMetric D O x y
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))
          + ENNReal.ofReal (n * ((ε : ℝ) / ((n : ℝ) + 1))) := key
    _ ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) + ENNReal.ofReal ε :=
        add_le_add le_rfl hbound
    _ = ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) + ε := by
        rw [ENNReal.ofReal_coe_nnreal]

/-- Upper bound of the chain formula by the length of a path in `O` (route Step 3.4, "partition an internal path and
approximate its partition points by dense vertices"). The clearance is bounded below along the compact image. -/
theorem chainDistance_le_pathLength (hD : IsEuclideanLengthMetric D) {O S Q : Set ℂ} (hO : IsOpen O)
    (hQ : Q ⊆ Oᶜ) (hS : O ⊆ closure S) {x y : ℂ} (γ : Path x y) (hγ : ∀ t, γ t ∈ O) :
    chainDistance S D Q x y ≤ pathLength D γ := by
  by_cases hL : pathLength D γ = ⊤
  · rw [hL]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hrange : ∀ s : ℝ, γ.extend s ∈ O := fun s => hγ _
  -- Step 1: a uniform lower bound `ρ > 0` for the distance from the path to `Oᶜ`.
  obtain ⟨ρ, hρ, hρle⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ∀ s ∈ Icc (0 : ℝ) 1, ∀ q ∈ Oᶜ, ρ ≤ D (γ.extend s) q := by
    by_cases hne : Oᶜ.Nonempty
    · have hK : IsCompact (γ.extend '' Icc (0 : ℝ) 1) := isCompact_Icc.image γ.continuous_extend
      have hKne : (γ.extend '' Icc (0 : ℝ) 1).Nonempty :=
        ⟨γ.extend 0, mem_image_of_mem _ (left_mem_Icc.mpr zero_le_one)⟩
      have hKO : γ.extend '' Icc (0 : ℝ) 1 ⊆ O := by
        rintro _ ⟨s, -, rfl⟩
        exact hrange s
      have hpos := hD.setDist_pos_of_compact_subset_open hK hKne hO hKO hne subset_rfl
      refine ⟨setDist D (γ.extend '' Icc (0 : ℝ) 1) Oᶜ, hpos, fun s hs q hq => ?_⟩
      exact setDist_le_of_nonneg D (isEuclideanLengthMetric_nonneg hD) (mem_image_of_mem _ hs) hq
    · exact ⟨1, one_pos, fun s _ q hq => absurd ⟨q, hq⟩ hne⟩
  -- Step 2: uniform continuity of `(s, t) ↦ D(γ s, γ t)` on `[0,1]²` gives a fine uniform partition.
  have hcont2 : Continuous (fun p : ℝ × ℝ => D (γ.extend p.1) (γ.extend p.2)) :=
    (continuous_uncurry_of_isEuclideanLengthMetric hD).comp
      ((γ.continuous_extend.comp continuous_fst).prodMk (γ.continuous_extend.comp continuous_snd))
  have hunif : UniformContinuousOn (fun p : ℝ × ℝ => D (γ.extend p.1) (γ.extend p.2))
      (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hcont2.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp hunif (ρ / 16) (by positivity)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N, hNpos, hNδ⟩ : ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < δ :=
    ⟨n + 1, Nat.succ_pos n, by push_cast; exact hn⟩
  have hN : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN0 : (N : ℝ) ≠ 0 := hN.ne'
  have hsI : ∀ j ≤ N, (j : ℝ) / N ∈ Icc (0 : ℝ) 1 := fun j hj =>
    ⟨by positivity, (div_le_one hN).mpr (by exact_mod_cast hj)⟩
  have hmesh : ∀ i < N, D (γ.extend ((i : ℝ) / N)) (γ.extend (((i + 1 : ℕ) : ℝ) / N)) < ρ / 16 := by
    intro i hi
    have hi1 : ((i + 1 : ℕ) : ℝ) / N ∈ Icc (0 : ℝ) 1 := hsI (i + 1) hi
    have hs : (i : ℝ) / N ∈ Icc (0 : ℝ) 1 := hsI i hi.le
    have hdist : dist (((i : ℝ) / N, ((i + 1 : ℕ) : ℝ) / N) : ℝ × ℝ) ((i : ℝ) / N, (i : ℝ) / N) < δ := by
      rw [Prod.dist_eq, dist_self, Real.dist_eq]
      have habs : |((i + 1 : ℕ) : ℝ) / N - (i : ℝ) / N| = 1 / N := by
        rw [← sub_div]
        push_cast
        rw [add_sub_cancel_left, abs_of_pos (by positivity)]
      rw [habs]
      exact max_lt (by positivity) hNδ
    have hF := hδ' _ ⟨hs, hi1⟩ _ ⟨hs, hs⟩ hdist
    dsimp only at hF
    rw [hD.self_eq_zero, Real.dist_eq, sub_zero,
      abs_of_nonneg (isEuclideanLengthMetric_nonneg hD _ _)] at hF
    exact hF
  -- Step 3: the approximation error `η`.
  obtain ⟨η, hη, hηρ, hηe⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ ρ / 64 ∧ (N : ℝ) * (2 * η) ≤ (ε : ℝ) := by
    refine ⟨min (ρ / 64) ((ε : ℝ) / (2 * N)), lt_min (by positivity) (by positivity), min_le_left _ _, ?_⟩
    have h1 : min (ρ / 64) ((ε : ℝ) / (2 * N)) ≤ (ε : ℝ) / (2 * N) := min_le_right _ _
    calc (N : ℝ) * (2 * min (ρ / 64) ((ε : ℝ) / (2 * N)))
        ≤ (N : ℝ) * (2 * ((ε : ℝ) / (2 * N))) := mul_le_mul_of_nonneg_left (by linarith) hN.le
      _ = (ε : ℝ) := by field_simp
  -- Step 4: the points `z i` of the uniform partition, and the chain vertices `vtx i`.
  have hap : ∀ i : ℕ, ∃ w ∈ S, D (γ.extend ((i : ℝ) / N)) w < η := fun i => by
    obtain ⟨w, hw, hlt⟩ := exists_lt_add_of_mem_closure hD (v := γ.extend ((i : ℝ) / N))
      (hS (hrange _)) hη
    refine ⟨w, hw, ?_⟩
    rwa [hD.self_eq_zero, zero_add] at hlt
  choose w hwS hwD using hap
  let z : ℕ → ℂ := fun i => γ.extend ((i : ℝ) / N)
  let vtx : ℕ → ℂ := fun i => if i = 0 then x else if i = N then y else w i
  have hz0 : z 0 = x := by simp [z]
  have hzN : z N = y := by
    simp only [z]
    rw [div_self hN0, Path.extend_one]
  have hv0 : vtx 0 = x := by simp [vtx]
  have hvN : vtx N = y := by simp [vtx, hNpos.ne']
  have hvS : ∀ i ≤ N, vtx i ∈ S ∪ {x, y} := by
    intro i _
    by_cases h0 : i = 0
    · rw [h0]
      simp [vtx]
    by_cases hN' : i = N
    · rw [hN']
      simp [vtx, hNpos.ne']
    · have : vtx i = w i := by simp [vtx, h0, hN']
      rw [this]
      exact Or.inl (hwS i)
  have hvz : ∀ i ≤ N, D (vtx i) (z i) ≤ η := by
    intro i _
    by_cases h0 : i = 0
    · rw [h0, hv0, hz0, hD.self_eq_zero]
      exact hη.le
    by_cases hN' : i = N
    · rw [hN', hvN, hzN, hD.self_eq_zero]
      exact hη.le
    have : vtx i = w i := by simp [vtx, h0, hN']
    rw [this, hD.symm]
    exact (hwD i).le
  -- Step 5: the clearance of every vertex is at least `ρ/2`, and every edge is permitted.
  have hclear : ∀ j ≤ N, ENNReal.ofReal (ρ / 2) ≤ clearance D Q (vtx j) := by
    intro j hj
    unfold clearance
    refine le_iInf₂ fun q hq => ENNReal.ofReal_le_ofReal ?_
    have h1 : ρ ≤ D (z j) q := hρle _ (hsI j hj) q (hQ hq)
    have h2 : D (z j) q ≤ D (z j) (vtx j) + D (vtx j) q := hD.triangle _ _ _
    have h3 : D (z j) (vtx j) ≤ η := by
      rw [hD.symm]
      exact hvz j hj
    linarith
  have hedge_dist : ∀ i < N, D (vtx i) (vtx (i + 1)) ≤ D (z i) (z (i + 1)) + 2 * η := by
    intro i hi
    have h1 : D (vtx i) (vtx (i + 1)) ≤ D (vtx i) (z i) + D (z i) (vtx (i + 1)) := hD.triangle _ _ _
    have h2 : D (z i) (vtx (i + 1)) ≤ D (z i) (z (i + 1)) + D (z (i + 1)) (vtx (i + 1)) :=
      hD.triangle _ _ _
    have h3 : D (vtx i) (z i) ≤ η := hvz i hi.le
    have h4 : D (z (i + 1)) (vtx (i + 1)) ≤ η := by
      rw [hD.symm]
      exact hvz (i + 1) hi
    linarith
  have hperm : ∀ i < N, PermittedEdge D Q (vtx i) (vtx (i + 1)) := by
    intro i hi
    have hd := hedge_dist i hi
    have hm : D (z i) (z (i + 1)) < ρ / 16 := hmesh i hi
    have hlt : 4 * ENNReal.ofReal (D (vtx i) (vtx (i + 1))) < ENNReal.ofReal (ρ / 2) := by
      have e4 : (4 : ℝ≥0∞) * ENNReal.ofReal (D (vtx i) (vtx (i + 1)))
          = ENNReal.ofReal (4 * D (vtx i) (vtx (i + 1))) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      rw [e4, ENNReal.ofReal_lt_ofReal_iff (half_pos hρ)]
      linarith
    exact lt_of_lt_of_le hlt (le_min (hclear i hi.le) (hclear (i + 1) hi))
  have hadm : AdmissibleChain S D Q x y N vtx := ⟨hv0, hvN, hvS, hperm⟩
  -- Step 6: the cost of this chain is at most the length of `γ` plus `ε`.
  have hcost : chainDistance S D Q x y ≤ ∑ i ∈ Finset.range N, ENNReal.ofReal (D (vtx i) (vtx (i + 1))) := by
    unfold chainDistance
    exact (iInf_le _ N).trans ((iInf_le _ vtx).trans (iInf_le _ hadm))
  have hpart : ∑ i ∈ Finset.range N, ENNReal.ofReal (D (z i) (z (i + 1))) ≤ pathLength D γ := by
    have hmono : Monotone (fun k : ℕ => ((min k N : ℕ) : ℝ) / N) := by
      intro a b hab
      exact div_le_div_of_nonneg_right (by exact_mod_cast min_le_min_right N hab) hN.le
    have hmem : ∀ k : ℕ, ((min k N : ℕ) : ℝ) / N ∈ Icc (0 : ℝ) 1 := fun k =>
      hsI (min k N) (min_le_right _ _)
    unfold pathLength curveLength
    refine le_iSup_of_le (N, ⟨fun k => ((min k N : ℕ) : ℝ) / N, hmono, hmem⟩) (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    have e1 : min (i + 1) N = i + 1 := min_eq_left (by omega)
    have e2 : min i N = i := min_eq_left (by omega)
    simp only [e1, e2]
    congr 1
    exact hD.symm _ _
  have hgeo : ∑ i ∈ Finset.range N, ENNReal.ofReal (D (vtx i) (vtx (i + 1)))
      ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (D (z i) (z (i + 1))) + ENNReal.ofReal (2 * η)) := by
    refine Finset.sum_le_sum fun i hi => ?_
    exact (ENNReal.ofReal_le_ofReal (hedge_dist i (Finset.mem_range.mp hi))).trans ENNReal.ofReal_add_le
  have hsum2 : ∑ i ∈ Finset.range N, ENNReal.ofReal (2 * η) = ENNReal.ofReal (N * (2 * η)) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
      ENNReal.ofReal_natCast]
  calc chainDistance S D Q x y
      ≤ ∑ i ∈ Finset.range N, ENNReal.ofReal (D (vtx i) (vtx (i + 1))) := hcost
    _ ≤ ∑ i ∈ Finset.range N, (ENNReal.ofReal (D (z i) (z (i + 1))) + ENNReal.ofReal (2 * η)) := hgeo
    _ = ∑ i ∈ Finset.range N, ENNReal.ofReal (D (z i) (z (i + 1))) + ENNReal.ofReal (N * (2 * η)) := by
        rw [Finset.sum_add_distrib, hsum2]
    _ ≤ pathLength D γ + ENNReal.ofReal (ε : ℝ) := add_le_add hpart (ENNReal.ofReal_le_ofReal hηe)
    _ = pathLength D γ + ε := by rw [ENNReal.ofReal_coe_nnreal]

/-- The chain formula is the internal metric on an open set `O` containing `x` (route Step 3.4): the infimum of the
costs of permitted chains recovers `D(x, y; O)` from a countable dense vertex set `S` and a countable set `Q` dense in
`ℂ ∖ O`, for a Euclidean length metric `D`. -/
theorem chainDistance_eq_internalMetric (hD : IsEuclideanLengthMetric D) {O S Q : Set ℂ} (hO : IsOpen O)
    (hQ : Q ⊆ Oᶜ) (hQd : Oᶜ ⊆ closure Q) (hS : O ⊆ closure S) {x y : ℂ} (hx : x ∈ O) :
    chainDistance S D Q x y = internalMetric D O x y := by
  refine le_antisymm ?_ (internalMetric_le_chainDistance hD hO hQd hx)
  unfold internalMetric
  exact le_iInf fun P => le_iInf fun hP => chainDistance_le_pathLength hD hO hQ hS P hP

end HarmonicBalls.S11m

