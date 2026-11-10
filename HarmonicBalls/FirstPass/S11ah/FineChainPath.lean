import Mathlib
import HarmonicBalls.FirstPass.S11ah.LengthBorelClauses

/-!
# Compact fine chains give a path (B1 of the Borel code, owner n3)

Ruling chat 236, section 4 (`compact_fine_chains_to_path`), in the form used by the reverse and the
forward implications of the length clause of `IsLengthMetricOn B (decoderOn B d)`.

Let `B ⊆ ℂ` and let `D : ℂ → ℂ → ℝ` satisfy the metric clauses on `B` (self, separation, symmetry,
triangle), continuity on `B × B`, and `V2 B D`. Let `K ⊆ B` be compact and `x y ∈ K`. Suppose that for
every `n` there is a finite chain `v 0 = x, …, v N = y` in `K` with `D`-mesh `≤ 1/(n+1)` and `D`-sum
`≤ L`. Then there is a path `P` from `x` to `y` inside `K` with `pathLength D P ≤ ENNReal.ofReal L`.

Proof (Armstrong–Kuusi–Mourrat style fine-chain argument, compact version). The step map `Φ n` sends
`u ∈ [0,1]` to the last vertex of the `n`-th chain whose partial sum is `≤ L u`. It satisfies
`D (Φ n s) (Φ n t) ≤ L |s - t| + 1/(n+1)`. A cluster point `g` of `(Φ n)` in the compact space
`[0,1] → K` (Tychonoff) satisfies `D (g s) (g t) ≤ L |s - t|`, with `g 0 = x`, `g 1 = y`. The
pointwise condition `V2` turns this `D`-Lipschitz bound into Euclidean continuity.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal
noncomputable section

namespace HarmonicBalls.FirstPassS11ahFineChainPath

open HarmonicBalls.FirstPassS11ahLengthBorelClauses FirstPassS11ah HarmonicBalls

/-! ### Partial sums of a chain and the last index below a level -/

/-- The partial sums `∑_{k<i} D(v k, v (k+1))` of a chain `v`. -/
def chainSum (D : ℂ → ℂ → ℝ) (v : ℕ → ℂ) (i : ℕ) : ℝ :=
  ∑ k ∈ Finset.range i, D (v k) (v (k + 1))

/-- The last index `i ≤ N` with `S i ≤ s`. -/
def chainIdx (N : ℕ) (S : ℕ → ℝ) (s : ℝ) : ℕ :=
  Nat.findGreatest (fun i => S i ≤ s) N

lemma chainIdx_le (N : ℕ) (S : ℕ → ℝ) (s : ℝ) : chainIdx N S s ≤ N :=
  Nat.findGreatest_le N

lemma chainIdx_spec {N : ℕ} {S : ℕ → ℝ} {s : ℝ} (h0 : S 0 ≤ s) : S (chainIdx N S s) ≤ s := by
  unfold chainIdx
  exact Nat.findGreatest_spec (P := fun i => S i ≤ s) (Nat.zero_le N) h0

lemma lt_chainIdx_succ {N : ℕ} {S : ℕ → ℝ} {s : ℝ} (hi : chainIdx N S s < N) :
    s < S (chainIdx N S s + 1) := by
  by_contra h
  have h' : S (chainIdx N S s + 1) ≤ s := not_lt.1 h
  have h2 : chainIdx N S s + 1 ≤ chainIdx N S s :=
    Nat.le_findGreatest (show chainIdx N S s + 1 ≤ N by omega) h'
  omega

lemma chainIdx_mono (N : ℕ) {S : ℕ → ℝ} {s t : ℝ} (h0 : S 0 ≤ s) (hst : s ≤ t) :
    chainIdx N S s ≤ chainIdx N S t :=
  Nat.le_findGreatest (chainIdx_le N S s) (le_trans (chainIdx_spec (N := N) h0) hst)

lemma chainIdx_eq_of_le {N : ℕ} {S : ℕ → ℝ} {s : ℝ} (h : S N ≤ s) : chainIdx N S s = N :=
  le_antisymm (chainIdx_le N S s) (Nat.le_findGreatest le_rfl h)

/-! ### Triangle inequality along a chain -/

lemma chain_dist_le {B : Set ℂ} {D : ℂ → ℂ → ℝ}
    (hself : ∀ z ∈ B, D z z = 0)
    (htri : ∀ u ∈ B, ∀ v ∈ B, ∀ w ∈ B, D u w ≤ D u v + D v w)
    {N : ℕ} {v : ℕ → ℂ} (hv : ∀ t ≤ N, v t ∈ B) {i : ℕ} :
    ∀ j, i ≤ j → j ≤ N → D (v i) (v j) ≤ chainSum D v j - chainSum D v i := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base =>
    intro hiN
    have h0 := hself _ (hv i hiN)
    simp [chainSum, h0]
  | succ j hij ih =>
    intro hjN
    have h1 := htri _ (hv i (by omega)) _ (hv j (by omega)) _ (hv (j + 1) hjN)
    have h2 := ih (by omega)
    unfold chainSum at *
    rw [Finset.sum_range_succ]
    linarith

lemma dist_nonneg_of_clauses {B : Set ℂ} {D : ℂ → ℂ → ℝ}
    (hself : ∀ z ∈ B, D z z = 0) (hsymm : ∀ z ∈ B, ∀ w ∈ B, D z w = D w z)
    (htri : ∀ u ∈ B, ∀ v ∈ B, ∀ w ∈ B, D u w ≤ D u v + D v w) {z w : ℂ} (hz : z ∈ B) (hw : w ∈ B) :
    0 ≤ D z w := by
  have h := htri z hz w hw z hz
  rw [hself z hz, hsymm w hw z hz] at h
  linarith

/-! ### The step estimate -/

/-- Step estimate: for `0 ≤ s ≤ t`, the vertices at the last indices below `s` and `t` are
`D`-within `t - s + μ`, when all chain mesh sizes are `≤ μ`. -/
lemma step_dist_le {B : Set ℂ} {D : ℂ → ℂ → ℝ}
    (hself : ∀ z ∈ B, D z z = 0)
    (htri : ∀ u ∈ B, ∀ v ∈ B, ∀ w ∈ B, D u w ≤ D u v + D v w)
    {N : ℕ} {v : ℕ → ℂ} (hv : ∀ t ≤ N, v t ∈ B) {μ : ℝ} (hμ : 0 ≤ μ)
    (hmesh : ∀ t < N, D (v t) (v (t + 1)) ≤ μ) {s t : ℝ} (h0s : 0 ≤ s) (hst : s ≤ t) :
    D (v (chainIdx N (chainSum D v) s)) (v (chainIdx N (chainSum D v) t)) ≤ (t - s) + μ := by
  have hS0s : chainSum D v 0 ≤ s := by simp [chainSum, h0s]
  have hS0t : chainSum D v 0 ≤ t := le_trans hS0s hst
  have hij := chainIdx_mono N hS0s hst
  have hjN := chainIdx_le N (chainSum D v) t
  have hiN := chainIdx_le N (chainSum D v) s
  have hbound := chain_dist_le hself htri hv (chainIdx N (chainSum D v) t) hij hjN
  have hSj : chainSum D v (chainIdx N (chainSum D v) t) ≤ t := chainIdx_spec hS0t
  by_cases hlt : chainIdx N (chainSum D v) s < N
  · have hsucc := lt_chainIdx_succ (N := N) (S := chainSum D v) (s := s) hlt
    have hstep : chainSum D v (chainIdx N (chainSum D v) s + 1) =
        chainSum D v (chainIdx N (chainSum D v) s) + D (v (chainIdx N (chainSum D v) s))
          (v (chainIdx N (chainSum D v) s + 1)) := by
      unfold chainSum; rw [Finset.sum_range_succ]
    have hmu := hmesh _ hlt
    linarith
  · have heq : chainIdx N (chainSum D v) s = N := by omega
    have hj : chainIdx N (chainSum D v) t = N := by omega
    rw [heq, hj]
    have h0 := hself _ (hv N le_rfl)
    rw [h0]
    linarith

/-- Two-sided version of `step_dist_le`, with `|t - s|`. -/
lemma step_dist_le_abs {B : Set ℂ} {D : ℂ → ℂ → ℝ}
    (hself : ∀ z ∈ B, D z z = 0) (hsymm : ∀ z ∈ B, ∀ w ∈ B, D z w = D w z)
    (htri : ∀ u ∈ B, ∀ v ∈ B, ∀ w ∈ B, D u w ≤ D u v + D v w)
    {N : ℕ} {v : ℕ → ℂ} (hv : ∀ t ≤ N, v t ∈ B) {μ : ℝ} (hμ : 0 ≤ μ)
    (hmesh : ∀ t < N, D (v t) (v (t + 1)) ≤ μ) {s t : ℝ} (h0s : 0 ≤ s) (h0t : 0 ≤ t) :
    D (v (chainIdx N (chainSum D v) s)) (v (chainIdx N (chainSum D v) t)) ≤ |t - s| + μ := by
  rcases le_total s t with hst | hts
  · have := step_dist_le hself htri hv hμ hmesh h0s hst
    rw [abs_of_nonneg (by linarith)]
    exact this
  · have := step_dist_le hself htri hv hμ hmesh h0t hts
    rw [hsymm _ (hv _ (chainIdx_le N _ _)) _ (hv _ (chainIdx_le N _ _))]
    rw [abs_of_nonpos (by linarith)]
    linarith

/-! ### From `D`-Lipschitz to Euclidean continuity (uses `V2`) -/

lemma continuous_of_lip_V2 {B : Set ℂ} {D : ℂ → ℂ → ℝ} (hV : V2 B D) {L : ℝ} (hL : 0 ≤ L)
    {f : unitInterval → ℂ} (hfB : ∀ s, f s ∈ B)
    (hlip : ∀ s t : unitInterval, D (f s) (f t) ≤ L * |(s : ℝ) - t|) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun s0 => Metric.continuousAt_iff.2 fun ε hε => ?_
  obtain ⟨e, he, hVe⟩ := hV (f s0) (hfB s0) ε hε
  refine ⟨e / (L + 1), by positivity, fun {t} ht => ?_⟩
  by_contra hcon
  have hcon' : ε ≤ dist (f t) (f s0) := not_lt.1 hcon
  have h1 := hVe (f t) (hfB t) hcon'
  have hd : |(s0 : ℝ) - t| < e / (L + 1) := by
    rw [abs_sub_comm, ← Real.dist_eq, ← Subtype.dist_eq]
    exact ht
  have hL' : L * |(s0 : ℝ) - t| < e := by
    calc L * |(s0 : ℝ) - t| ≤ L * (e / (L + 1)) := mul_le_mul_of_nonneg_left hd.le hL
      _ < e := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have h2 := hlip s0 t
  linarith

/-! ### Length of a path from a `D`-Lipschitz bound -/

lemma pathLength_le_of_lip {D : ℂ → ℂ → ℝ} {x y : ℂ} (P : Path x y) {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ s t : unitInterval, D (P s) (P t) ≤ L * |(s : ℝ) - t|) :
    pathLength D P ≤ ENNReal.ofReal L := by
  have hext : ∀ t (ht : t ∈ Icc (0 : ℝ) 1), P.extend t = P ⟨t, ht⟩ :=
    fun t ht => Path.extend_extends' P ⟨t, ht⟩
  unfold pathLength curveLength
  refine iSup_le fun q => ?_
  obtain ⟨N', u, hmono, hmem⟩ := q
  have hterm : ∀ i ∈ Finset.range N',
      ENNReal.ofReal (D (P.extend (u (i + 1))) (P.extend (u i))) ≤
        ENNReal.ofReal (L * (u (i + 1) - u i)) := by
    intro i _
    apply ENNReal.ofReal_le_ofReal
    rw [hext _ (hmem _), hext _ (hmem _)]
    have h := hlip ⟨u (i + 1), hmem (i + 1)⟩ ⟨u i, hmem i⟩
    have hle : u i ≤ u (i + 1) := hmono (Nat.le_succ i)
    rw [abs_of_nonneg (sub_nonneg.2 hle)] at h
    exact h
  have hsum_nonneg : ∀ i ∈ Finset.range N', 0 ≤ L * (u (i + 1) - u i) := fun i _ =>
    mul_nonneg hL (sub_nonneg.2 (hmono (Nat.le_succ i)))
  have htel : ∑ i ∈ Finset.range N', L * (u (i + 1) - u i) ≤ L := by
    rw [← Finset.mul_sum, Finset.sum_range_sub u N']
    have h1 : u N' - u 0 ≤ 1 := by linarith [(hmem N').2, (hmem 0).1]
    exact mul_le_of_le_one_right hL h1
  calc ∑ i ∈ Finset.range N', ENNReal.ofReal (D (P.extend (u (i + 1))) (P.extend (u i)))
      ≤ ∑ i ∈ Finset.range N', ENNReal.ofReal (L * (u (i + 1) - u i)) :=
        Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ i ∈ Finset.range N', L * (u (i + 1) - u i)) :=
        (ENNReal.ofReal_sum_of_nonneg hsum_nonneg).symm
    _ ≤ ENNReal.ofReal L := ENNReal.ofReal_le_ofReal htel

/-! ### Cluster points in a compact product -/

lemma mem_of_mapClusterPt' {α : Type*} [TopologicalSpace α] {g : α} {Φ : ℕ → α}
    (hg : MapClusterPt g atTop Φ) {S : Set α} (hS : IsClosed S)
    (hev : ∀ᶠ n in atTop, Φ n ∈ S) : g ∈ S := by
  have h1 : Filter.map Φ atTop ≤ 𝓟 S := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    exact hev
  have h2 : ClusterPt g (𝓟 S) := ClusterPt.mono hg h1
  rw [← hS.closure_eq]
  exact mem_closure_iff_clusterPt.2 h2

/-! ### The compact fine-chain lemma -/

/-- **Compact fine chains give a path** (ruling chat 236, section 4). Let `K ⊆ B` be compact and
`x, y ∈ K`. If for every mesh `1/(n+1)` there is a chain in `K` from `x` to `y` with `D`-mesh
`≤ 1/(n+1)` and `D`-sum `≤ L`, then some path in `K` from `x` to `y` has `pathLength D ≤ ofReal L`. -/
theorem exists_path_of_fine_chains {B K : Set ℂ} {D : ℂ → ℂ → ℝ} {x y : ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hKc : IsCompact K) (hKB : K ⊆ B)
    (hself : ∀ z ∈ B, D z z = 0) (hsymm : ∀ z ∈ B, ∀ w ∈ B, D z w = D w z)
    (htri : ∀ u ∈ B, ∀ v ∈ B, ∀ w ∈ B, D u w ≤ D u v + D v w)
    (hsep : ∀ z ∈ B, ∀ w ∈ B, D z w = 0 → z = w)
    (hcont : ContinuousOn (fun p : ℂ × ℂ => D p.1 p.2) (B ×ˢ B))
    (hV : V2 B D)
    (hchain : ∀ n : ℕ, ∃ N : ℕ, ∃ v : ℕ → ℂ, v 0 = x ∧ v N = y ∧ (∀ t ≤ N, v t ∈ K) ∧
      (∀ t < N, D (v t) (v (t + 1)) ≤ 1 / ((n : ℝ) + 1)) ∧ chainSum D v N ≤ L) :
    ∃ P : Path x y, (∀ t, P t ∈ K) ∧ pathLength D P ≤ ENNReal.ofReal L := by
  classical
  have : CompactSpace K := isCompact_iff_compactSpace.mp hKc
  choose N v hv0 hvN hvK hmesh hsum using hchain
  have hvB : ∀ n, ∀ t ≤ N n, v n t ∈ B := fun n t ht => hKB (hvK n t ht)
  have hmu : ∀ n : ℕ, (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := fun n => by positivity
  have h0u : ((0 : unitInterval) : ℝ) = 0 := rfl
  have h1u : ((1 : unitInterval) : ℝ) = 1 := rfl
  -- the step maps `Φ n : [0,1] → K`
  let Φ : ℕ → unitInterval → K := fun n u =>
    ⟨v n (chainIdx (N n) (chainSum D (v n)) (L * u)), hvK n _ (chainIdx_le _ _ _)⟩
  have hΦval : ∀ n u, (Φ n u : ℂ) = v n (chainIdx (N n) (chainSum D (v n)) (L * u)) :=
    fun _ _ => rfl
  have hΦlip : ∀ n (s t : unitInterval),
      D (Φ n s : ℂ) (Φ n t : ℂ) ≤ L * |(s : ℝ) - t| + 1 / ((n : ℝ) + 1) := by
    intro n s t
    rw [hΦval, hΦval]
    have h := step_dist_le_abs hself hsymm htri (hvB n) (hmu n) (hmesh n)
      (mul_nonneg hL s.2.1) (mul_nonneg hL t.2.1)
    have habs : |L * (t : ℝ) - L * (s : ℝ)| = L * |(s : ℝ) - t| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg hL, abs_sub_comm]
    rw [habs] at h
    exact h
  have hΦ0 : ∀ n, (Φ n 0 : ℂ) = x := by
    intro n
    rw [hΦval, h0u, mul_zero]
    have hS00 : chainSum D (v n) 0 = 0 := by simp [chainSum]
    have hsp : chainSum D (v n) (chainIdx (N n) (chainSum D (v n)) 0) ≤ 0 :=
      chainIdx_spec (by rw [hS00])
    have hb := chain_dist_le hself htri (hvB n) (i := 0)
      (chainIdx (N n) (chainSum D (v n)) 0) (Nat.zero_le _) (chainIdx_le _ _ _)
    have hnn : 0 ≤ D (v n 0) (v n (chainIdx (N n) (chainSum D (v n)) 0)) :=
      dist_nonneg_of_clauses hself hsymm htri (hvB n 0 (Nat.zero_le _))
        (hvB n (chainIdx (N n) (chainSum D (v n)) 0) (chainIdx_le _ _ _))
    have h0 : D (v n 0) (v n (chainIdx (N n) (chainSum D (v n)) 0)) = 0 :=
      le_antisymm (by linarith) hnn
    have := hsep _ (hvB n 0 (Nat.zero_le _)) _ (hvB n _ (chainIdx_le _ _ _)) h0
    rw [hv0 n] at this
    exact this.symm
  have hΦ1 : ∀ n, (Φ n 1 : ℂ) = y := by
    intro n
    rw [hΦval, h1u, mul_one, chainIdx_eq_of_le (hsum n), hvN n]
  -- a cluster point in the compact product `[0,1] → K`
  obtain ⟨g, -, hg⟩ := isCompact_univ.exists_mapClusterPt (f := atTop) (u := Φ) (by simp)
  have hglip : ∀ s t : unitInterval, D (g s : ℂ) (g t : ℂ) ≤ L * |(s : ℝ) - t| := by
    intro s t
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n0, hn0⟩ := exists_nat_one_div_lt hε
    have hc1 : Continuous (fun φ : unitInterval → K => D (φ s : ℂ) (φ t : ℂ)) := by
      have hc : Continuous (fun φ : unitInterval → K => ((φ s : ℂ), (φ t : ℂ))) :=
        (continuous_subtype_val.comp (continuous_apply s)).prodMk
          (continuous_subtype_val.comp (continuous_apply t))
      exact hcont.comp_continuous hc (fun φ => mk_mem_prod (hKB (φ s).2) (hKB (φ t).2))
    have hev : ∀ᶠ n in atTop, Φ n ∈
        {φ : unitInterval → K | D (φ s : ℂ) (φ t : ℂ) ≤ L * |(s : ℝ) - t| + ε} := by
      filter_upwards [eventually_ge_atTop n0] with n hn
      have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
      have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((n0 : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      show D (Φ n s : ℂ) (Φ n t : ℂ) ≤ _
      linarith [hΦlip n s t]
    exact mem_of_mapClusterPt' hg (isClosed_le hc1 continuous_const) hev
  have hg0 : (g 0 : ℂ) = x :=
    mem_of_mapClusterPt' hg
      (isClosed_eq (continuous_subtype_val.comp (continuous_apply (0 : unitInterval)))
        continuous_const)
      (Filter.Eventually.of_forall fun n => hΦ0 n)
  have hg1 : (g 1 : ℂ) = y :=
    mem_of_mapClusterPt' hg
      (isClosed_eq (continuous_subtype_val.comp (continuous_apply (1 : unitInterval)))
        continuous_const)
      (Filter.Eventually.of_forall fun n => hΦ1 n)
  have hgB : ∀ s, (g s : ℂ) ∈ B := fun s => hKB (g s).2
  have hcontP : Continuous (fun s : unitInterval => (g s : ℂ)) :=
    continuous_of_lip_V2 hV hL hgB hglip
  let P : Path x y :=
    { toFun := fun s => (g s : ℂ)
      continuous_toFun := hcontP
      source' := hg0
      target' := hg1 }
  exact ⟨P, fun t => (g t).2, pathLength_le_of_lip P hL hglip⟩

end HarmonicBalls.FirstPassS11ahFineChainPath
