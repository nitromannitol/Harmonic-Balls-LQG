import HarmonicBalls.FirstPass.S11ac.PathSubdivision
import HarmonicBalls.FirstPass.S11ac.Lebesgue
import HarmonicBalls.FirstPass.S11ac.LocalIdentity
import HarmonicBalls.Steps.Sec11.InternalMetricPaths
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity

/-! # Chain representation of the internal metric of an open set by pieces

Generic and deterministic. Let `D` be a Euclidean length metric, `X` open, and `Dp j` open pieces with `Dp j ⊆ X` covering
`X`. Let `cost j z w = b * internalMetric D (Dp j) z w` on `Dp j × Dp j`. Then the infimum of the costs of piece-chains
from `x` to `y` (vertices in `Q` except the endpoints) equals `b * internalMetric D X x y`.
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology unitInterval Metric
open scoped ENNReal

variable {D : ℂ → ℂ → ℝ}

theorem D_nonneg (hD : IsEuclideanLengthMetric D) (x y : ℂ) : 0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- Triangle inequality along a chain for the internal metric of an open set. -/
theorem internalMetric_chain_le (hD : IsEuclideanLengthMetric D) {U : Set ℂ} (hU : IsOpen U) (n : ℕ)
    (q : ℕ → ℂ) (hq : ∀ i ≤ n, q i ∈ U) :
    internalMetric D U (q 0) (q n) ≤ ∑ i ∈ Finset.range n, internalMetric D U (q i) (q (i + 1)) := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact le_of_eq (hD.internalMetric_self_of_mem_open (D_nonneg hD) hU (hq 0 (Nat.zero_le 0)))
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have ih' := ih (fun i hi => hq i (Nat.le_succ_of_le hi))
    calc internalMetric D U (q 0) (q (n + 1))
        ≤ internalMetric D U (q 0) (q n) + internalMetric D U (q n) (q (n + 1)) :=
          hD.internalMetric_triangle U _ _ _
      _ ≤ _ := by gcongr

/-- Monotonicity of the internal metric in the domain (antitone). -/
theorem internalMetric_anti {U V : Set ℂ} (hUV : U ⊆ V) (z w : ℂ) :
    internalMetric D V z w ≤ internalMetric D U z w := by
  unfold internalMetric
  exact le_iInf₂ fun P hP => iInf₂_le P (fun t => hUV (hP t))

/-- Admissible chains of pieces from `x` to `y`: interior vertices in `Q`, consecutive vertices in the same piece. -/
def PieceChain (Dp : ℕ → Set ℂ) (Q : Set ℂ) (x y : ℂ) (n : ℕ) (j : ℕ → ℕ) (q : ℕ → ℂ) : Prop :=
  q 0 = x ∧ q n = y ∧ (∀ i, 0 < i → i < n → q i ∈ Q) ∧ ∀ i < n, q i ∈ Dp (j i) ∧ q (i + 1) ∈ Dp (j i)

/-- The infimum of the piece-chain costs. -/
noncomputable def chainInf (cost : ℕ → ℂ → ℂ → ℝ≥0∞) (Dp : ℕ → Set ℂ) (Q : Set ℂ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ (n : ℕ) (j : ℕ → ℕ) (q : ℕ → ℂ) (_ : PieceChain Dp Q x y n j q),
    ∑ i ∈ Finset.range n, cost (j i) (q i) (q (i + 1))

/-- Lower bound: every piece-chain costs at least `b * internalMetric D X x y`. -/
theorem le_chainInf (hD : IsEuclideanLengthMetric D) {X : Set ℂ} (hX : IsOpen X) {Dp : ℕ → Set ℂ}
    (hDpX : ∀ j, Dp j ⊆ X) {Q : Set ℂ} {cost : ℕ → ℂ → ℂ → ℝ≥0∞} {b : ℝ≥0∞}
    (hcost : ∀ j z w, z ∈ Dp j → w ∈ Dp j → cost j z w = b * internalMetric D (Dp j) z w)
    {x y : ℂ} (hy : y ∈ X) :
    b * internalMetric D X x y ≤ chainInf cost Dp Q x y := by
  unfold chainInf
  refine le_iInf fun n => le_iInf fun j => le_iInf fun q => le_iInf fun hq => ?_
  obtain ⟨h0, hn, -, hmem⟩ := hq
  have hqX : ∀ i ≤ n, q i ∈ X := by
    intro i hi
    rcases Nat.lt_or_ge i n with h | h
    · exact hDpX (j i) (hmem i h).1
    · have hin : i = n := le_antisymm hi h
      rw [hin, hn]
      exact hy
  have htri := internalMetric_chain_le hD hX n q hqX
  rw [h0, hn] at htri
  calc b * internalMetric D X x y
      ≤ b * ∑ i ∈ Finset.range n, internalMetric D X (q i) (q (i + 1)) := by
        exact mul_le_mul' le_rfl htri
    _ ≤ b * ∑ i ∈ Finset.range n, internalMetric D (Dp (j i)) (q i) (q (i + 1)) := by
        refine mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => internalMetric_anti (hDpX (j i)) _ _)
    _ = ∑ i ∈ Finset.range n, b * internalMetric D (Dp (j i)) (q i) (q (i + 1)) := by
        rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range n, cost (j i) (q i) (q (i + 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        obtain ⟨h1, h2⟩ := hmem i (Finset.mem_range.1 hi)
        exact (hcost _ _ _ h1 h2).symm

/-- A finite family of positive reals has a uniform positive lower bound on an initial segment. -/
theorem exists_uniform_pos (ε : ℕ → ℝ) (hε : ∀ i, 0 < ε i) (N : ℕ) : ∃ E > 0, ∀ i < N, E ≤ ε i := by
  induction N with
  | zero => exact ⟨1, one_pos, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ n ih =>
    obtain ⟨E, hE, hEi⟩ := ih
    refine ⟨min E (ε n), lt_min hE (hε n), fun i hi => ?_⟩
    rcases (show i < n ∨ i = n by omega) with h | h
    · exact (min_le_left _ _).trans (hEi i h)
    · subst h
      exact min_le_right _ _

/-- Upper bound: a path in `X` yields a piece-chain with vertices in `Q` of cost at most `b * pathLength + η`. -/
theorem chainInf_le_of_path (hD : IsEuclideanLengthMetric D) {X : Set ℂ}
    {Dp : ℕ → Set ℂ} (hDpo : ∀ j, IsOpen (Dp j)) (hcov : X ⊆ ⋃ j, Dp j)
    {Q : Set ℂ} (hQd : X ⊆ closure Q)
    {cost : ℕ → ℂ → ℂ → ℝ≥0∞} {b : ℝ≥0∞} (hb : b ≠ ⊤)
    (hcost : ∀ j z w, z ∈ Dp j → w ∈ Dp j → cost j z w = b * internalMetric D (Dp j) z w)
    {x y : ℂ} (γ : Path x y) (hγX : ∀ t, γ t ∈ X) (hL : pathLength D γ ≠ ⊤)
    {η : ℝ≥0∞} (hη0 : η ≠ 0) :
    chainInf cost Dp Q x y ≤ b * pathLength D γ + η := by
  have hX' : ∀ t ∈ Icc (0 : ℝ) 1, γ.extend t ∈ X := fun t ht => by
    have h1 : γ.extend t = γ ⟨t, ht⟩ := Path.extend_extends' γ ⟨t, ht⟩
    rw [h1]
    exact hγX _
  have hXall : ∀ t, γ.extend t ∈ X := fun t => by
    exact hγX _
  obtain ⟨N, u, j, hNpos, hu, hu0, huN, hsub⟩ := exists_subdivision_of_cover γ Dp hDpo
    (fun t ht => mem_iUnion.1 (hcov (hX' t ht)))
  have hx0 : γ.extend (u 0) = x := by
    rw [hu0]
    exact Path.extend_zero γ
  have hyN : γ.extend (u N) = y := by
    rw [huN]
    exact Path.extend_one γ
  -- the vertices of the subdivision
  have hvi : ∀ i < N, γ.extend (u i) ∈ Dp (j i) := fun i hi =>
    hsub i hi (u i) ⟨le_rfl, hu (Nat.le_succ i)⟩
  have hvi1 : ∀ i < N, γ.extend (u (i + 1)) ∈ Dp (j i) := fun i hi =>
    hsub i hi (u (i + 1)) ⟨hu (Nat.le_succ i), le_rfl⟩
  have hint : ∀ i < N, internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1))) ≠ ⊤ := by
    intro i hi
    have hle : internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1))) ≤ pathLength D γ := by
      refine le_trans ?_ (sum_internalMetric_le_pathLength hD γ N u hu hu0 huN (fun k => Dp (j k))
        (fun k hk t ht => hsub k hk t ht))
      exact Finset.single_le_sum (f := fun k => internalMetric D (Dp (j k)) (γ.extend (u k))
        (γ.extend (u (k + 1)))) (fun _ _ => zero_le) (Finset.mem_range.2 hi)
    exact ne_top_of_le_ne_top hL hle
  -- edge continuity: a uniform radius for each edge
  have hedge : ∀ i, ∃ ε : ℝ, 0 < ε ∧ (i < N → ∀ a c : ℂ, dist a (γ.extend (u i)) < ε →
      dist c (γ.extend (u (i + 1))) < ε →
      cost (j i) a c < b * internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1))) + η / (N : ℝ≥0∞)) := by
    intro i
    by_cases hi : i < N
    · have hs0 : η / (N : ℝ≥0∞) ≠ 0 := (ENNReal.div_pos_iff.2 ⟨hη0, ENNReal.natCast_ne_top N⟩).ne'
      have hfin : b * internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1))) ≠ ⊤ :=
        ENNReal.mul_ne_top hb (hint i hi)
      have hT : Tendsto (fun p : ℂ × ℂ => cost (j i) p.1 p.2) (𝓝 (γ.extend (u i), γ.extend (u (i + 1))))
          (𝓝 (b * internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1))))) := by
        have hc1 := hD.continuousAt_internalMetric_pair (D_nonneg hD) (hDpo (j i)) (hvi i hi) (hvi1 i hi)
        have hc2 := ENNReal.Tendsto.const_mul hc1 (Or.inr hb)
        refine hc2.congr' ?_
        filter_upwards [((hDpo (j i)).prod (hDpo (j i))).mem_nhds ⟨hvi i hi, hvi1 i hi⟩] with p hp
        exact (hcost (j i) _ _ hp.1 hp.2).symm
      have hlt := ENNReal.lt_add_right hfin hs0
      obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (Filter.Tendsto.eventually_lt_const hlt hT)
      refine ⟨ε, hε, fun _ a c ha hc => ?_⟩
      have hd : dist (a, c) (γ.extend (u i), γ.extend (u (i + 1))) < ε := by
        rw [Prod.dist_eq]
        exact max_lt ha hc
      exact hεP hd
    · exact ⟨1, one_pos, fun h => absurd h hi⟩
  choose ε hεpos hεP using hedge
  obtain ⟨E, hE, hEi⟩ := exists_uniform_pos ε hεpos N
  -- interior radii keeping the vertex inside the two adjacent pieces
  have hρ : ∀ k, ∃ ρ : ℝ, 0 < ρ ∧ (0 < k → k < N → Metric.ball (γ.extend (u k)) ρ ⊆ Dp (j (k - 1)) ∩ Dp (j k)) := by
    intro k
    by_cases hk : 0 < k ∧ k < N
    · have hmem1 : γ.extend (u k) ∈ Dp (j k) := hvi k hk.2
      have hmem0 : γ.extend (u k) ∈ Dp (j (k - 1)) := by
        have hkk : k - 1 + 1 = k := by omega
        exact hsub (k - 1) (by omega) (u k) (by rw [hkk]; exact ⟨hu (by omega), le_rfl⟩)
      obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 ((hDpo (j (k - 1))).inter (hDpo (j k)))
        (γ.extend (u k)) ⟨hmem0, hmem1⟩
      exact ⟨ρ, hρ, fun _ _ => hball⟩
    · exact ⟨1, one_pos, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
  choose ρ hρpos hρsub using hρ
  -- the chain vertices
  have hQk : ∀ k, ∃ z ∈ Q, dist z (γ.extend (u k)) < min E (ρ k) := fun k => by
    obtain ⟨w, hw, hd⟩ := Metric.mem_closure_iff.1 (hQd (hXall (u k))) _ (lt_min hE (hρpos k))
    exact ⟨w, hw, by rw [dist_comm]; exact hd⟩
  choose z hzQ hzd using hQk
  let q : ℕ → ℂ := fun k => if k = 0 then x else if k = N then y else z k
  have hq0 : q 0 = x := by simp [q]
  have hqN : q N = y := by simp [q, hNpos.ne']
  have hqint : ∀ k, 0 < k → k < N → q k = z k := fun k hk0 hkN => by
    simp [q, hk0.ne', hkN.ne]
  have hqd : ∀ k ≤ N, dist (q k) (γ.extend (u k)) < E := by
    intro k hk
    rcases Nat.eq_zero_or_pos k with h0 | hpos
    · rw [h0, hq0, hx0, dist_self]
      exact hE
    rcases (show k < N ∨ k = N by omega) with hlt | heq
    · rw [hqint k hpos hlt]
      exact lt_of_lt_of_le (hzd k) (min_le_left _ _)
    · rw [heq, hqN, hyN, dist_self]
      exact hE
  have hPC : PieceChain Dp Q x y N j q := by
    refine ⟨hq0, hqN, fun k hk0 hkN => ?_, fun i hi => ⟨?_, ?_⟩⟩
    · rw [hqint k hk0 hkN]
      exact hzQ k
    · rcases Nat.eq_zero_or_pos i with h0 | hpos
      · rw [h0, hq0, ← hx0]
        exact hvi 0 hNpos
      · rw [hqint i hpos hi]
        exact (hρsub i hpos hi (Metric.mem_ball.2 (lt_of_lt_of_le (hzd i) (min_le_right _ _)))).2
    · rcases (show i + 1 < N ∨ i + 1 = N by omega) with hlt | heq
      · rw [hqint (i + 1) (Nat.succ_pos i) hlt]
        have h := hρsub (i + 1) (Nat.succ_pos i) hlt
          (Metric.mem_ball.2 (lt_of_lt_of_le (hzd (i + 1)) (min_le_right _ _)))
        simpa using h.1
      · rw [heq, hqN, ← hyN]
        have h := hvi1 i hi
        rw [heq] at h
        exact h
  have hedgeq : ∀ i < N, cost (j i) (q i) (q (i + 1)) ≤
      b * internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1))) + η / (N : ℝ≥0∞) := by
    intro i hi
    exact (hεP i hi (q i) (q (i + 1)) (lt_of_lt_of_le (hqd i (by omega)) (hEi i hi))
      (lt_of_lt_of_le (hqd (i + 1) (by omega)) (hEi i hi))).le
  have hsum_le : ∑ i ∈ Finset.range N, cost (j i) (q i) (q (i + 1)) ≤
      ∑ i ∈ Finset.range N, (b * internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1)))
        + η / (N : ℝ≥0∞)) :=
    Finset.sum_le_sum fun i hi => hedgeq i (Finset.mem_range.1 hi)
  have hpath : ∑ i ∈ Finset.range N, internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1)))
      ≤ pathLength D γ :=
    sum_internalMetric_le_pathLength hD γ N u hu hu0 huN (fun k => Dp (j k)) (fun k hk t ht => hsub k hk t ht)
  have hNs : (N : ℝ≥0∞) * (η / (N : ℝ≥0∞)) ≤ η := ENNReal.mul_div_le
  unfold chainInf
  calc (⨅ (n : ℕ) (j : ℕ → ℕ) (q : ℕ → ℂ) (_ : PieceChain Dp Q x y n j q),
        ∑ i ∈ Finset.range n, cost (j i) (q i) (q (i + 1)))
      ≤ ∑ i ∈ Finset.range N, cost (j i) (q i) (q (i + 1)) :=
        iInf_le_of_le N (iInf_le_of_le j (iInf_le_of_le q (iInf_le_of_le hPC le_rfl)))
    _ ≤ ∑ i ∈ Finset.range N, (b * internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1)))
        + η / (N : ℝ≥0∞)) := hsum_le
    _ = b * ∑ i ∈ Finset.range N, internalMetric D (Dp (j i)) (γ.extend (u i)) (γ.extend (u (i + 1)))
        + (N : ℝ≥0∞) * (η / (N : ℝ≥0∞)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ b * pathLength D γ + η := add_le_add (mul_le_mul' le_rfl hpath) hNs

/-- **Chain identity.** For `x, y ∈ X` (open), the infimum of piece-chain costs equals `b * internalMetric D X x y`. -/
theorem chainInf_eq (hD : IsEuclideanLengthMetric D) {X : Set ℂ} (hX : IsOpen X)
    {Dp : ℕ → Set ℂ} (hDpX : ∀ j, Dp j ⊆ X) (hDpo : ∀ j, IsOpen (Dp j)) (hcov : X ⊆ ⋃ j, Dp j)
    {Q : Set ℂ} (hQd : X ⊆ closure Q)
    {cost : ℕ → ℂ → ℂ → ℝ≥0∞} {b : ℝ≥0∞} (hb0 : b ≠ 0) (hb : b ≠ ⊤)
    (hcost : ∀ j z w, z ∈ Dp j → w ∈ Dp j → cost j z w = b * internalMetric D (Dp j) z w)
    {x y : ℂ} (hy : y ∈ X) :
    chainInf cost Dp Q x y = b * internalMetric D X x y := by
  refine le_antisymm ?_ (le_chainInf hD hX hDpX hcost hy)
  by_cases ht : internalMetric D X x y = ⊤
  · rw [ht, ENNReal.mul_top hb0]
    exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (ε : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.2 hε.ne'
  have hη0 : (ε : ℝ≥0∞) / 2 ≠ 0 := (ENNReal.div_pos_iff.2 ⟨hε', ENNReal.ofNat_ne_top⟩).ne'
  have hδ0 : (ε : ℝ≥0∞) / 2 / (b + 1) ≠ 0 :=
    (ENNReal.div_pos_iff.2 ⟨hη0, ENNReal.add_ne_top.2 ⟨hb, ENNReal.one_ne_top⟩⟩).ne'
  have hδt : (ε : ℝ≥0∞) / 2 / (b + 1) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.div_ne_top ENNReal.coe_ne_top (by norm_num)) (by simp)
  have hlt : internalMetric D X x y < internalMetric D X x y + (ε : ℝ≥0∞) / 2 / (b + 1) :=
    ENNReal.lt_add_right ht hδ0
  obtain ⟨P, hP⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hPX, hPlt⟩ := iInf_lt_iff.1 hP
  have hPfin : pathLength D P ≠ ⊤ := by
    have hlt_top : internalMetric D X x y + (ε : ℝ≥0∞) / 2 / (b + 1) < ⊤ :=
      ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 ht, hδt.lt_top⟩
    exact ne_top_of_lt (hPlt.trans hlt_top)
  have hle := chainInf_le_of_path hD hDpo hcov hQd hb hcost P hPX hPfin hη0
  have hbδ : b * ((ε : ℝ≥0∞) / 2 / (b + 1)) ≤ (ε : ℝ≥0∞) / 2 := by
    calc b * ((ε : ℝ≥0∞) / 2 / (b + 1)) ≤ (b + 1) * ((ε : ℝ≥0∞) / 2 / (b + 1)) :=
          mul_le_mul' le_self_add le_rfl
      _ ≤ (ε : ℝ≥0∞) / 2 := ENNReal.mul_div_le
  have hbound : b * pathLength D P ≤ b * internalMetric D X x y + (ε : ℝ≥0∞) / 2 := by
    calc b * pathLength D P ≤ b * (internalMetric D X x y + (ε : ℝ≥0∞) / 2 / (b + 1)) :=
          mul_le_mul' le_rfl hPlt.le
      _ = b * internalMetric D X x y + b * ((ε : ℝ≥0∞) / 2 / (b + 1)) := mul_add _ _ _
      _ ≤ b * internalMetric D X x y + (ε : ℝ≥0∞) / 2 := add_le_add le_rfl hbδ
  calc chainInf cost Dp Q x y ≤ b * pathLength D P + (ε : ℝ≥0∞) / 2 := hle
    _ ≤ (b * internalMetric D X x y + (ε : ℝ≥0∞) / 2) + (ε : ℝ≥0∞) / 2 := add_le_add hbound le_rfl
    _ = b * internalMetric D X x y + (ε : ℝ≥0∞) := by rw [add_assoc, ENNReal.add_halves]

end HarmonicBalls.S11ac

#print axioms HarmonicBalls.S11ac.chainInf_eq
