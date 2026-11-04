import HarmonicBalls.Steps.Sec11.BoundaryClearanceChains

/-! # Stability of boundary-clearance edges -/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- Every edge with a strict real clearance also has a positive rational
clearance. -/
theorem exists_rational_boundary_clearance
    {D : ℂ → ℂ → ℝ} (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} {x y : ℂ} {δ : ℝ}
    (hxy : D x y < δ) (hclear : ∀ z ∉ U, δ ≤ D x z) :
    ∃ q : ℚ, 0 < q ∧ D x y < (q : ℝ) ∧ ∀ z ∉ U, (q : ℝ) ≤ D x z := by
  obtain ⟨q, hq₁, hq₂⟩ := exists_rat_btwn hxy
  have hq : 0 < (q : ℝ) := lt_of_le_of_lt (hnonneg x y) hq₁
  refine ⟨q, by exact_mod_cast hq, hq₁, ?_⟩
  intro z hz
  exact hq₂.le.trans (hclear z hz)

/-- A strict clearance edge remains a clearance edge when both endpoints are
perturbed by less than one third of its clearance margin. -/
theorem IsEuclideanLengthMetric.boundary_clearance_stable
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {U : Set ℂ} {x y x' y' : ℂ} {δ ε : ℝ}
    (hmargin : D x y + 3 * ε < δ)
    (hx : D x x' < ε) (hy : D y y' < ε)
    (hclear : ∀ z ∉ U, δ ≤ D x z) :
    D x' y' < δ - ε ∧ ∀ z ∉ U, δ - ε ≤ D x' z := by
  have h₁ := hD.triangle x' x y'
  have h₂ := hD.triangle x y y'
  have hx' : D x' x < ε := by simpa only [hD.symm x' x] using hx
  refine ⟨by linarith, ?_⟩
  intro z hz
  have hz' := hclear z hz
  have ht := hD.triangle x x' z
  linarith

/-- The cost of a clearance edge changes by at most the sum of endpoint
perturbations. -/
theorem IsEuclideanLengthMetric.distance_perturb_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (x y x' y' : ℂ) :
    D x' y' ≤ D x x' + D x y + D y y' := by
  have h₁ := hD.triangle x' x y'
  have h₂ := hD.triangle x y y'
  rw [hD.symm x' x] at h₁
  linarith

/-- A finite chain of clearance edges has a common positive perturbation
margin. -/
theorem finite_chain_boundary_clearance_margin
    {D : ℂ → ℂ → ℝ} {U : Set ℂ} (v : ℕ → ℂ) (n : ℕ)
    (hchain : ∀ i < n, ∃ δ : ℝ, D (v i) (v (i + 1)) < δ ∧
      ∀ z ∉ U, δ ≤ D (v i) z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i < n, ∃ δ : ℝ,
      D (v i) (v (i + 1)) + 3 * ε < δ ∧ ∀ z ∉ U, δ ≤ D (v i) z := by
  induction n with
  | zero =>
    refine ⟨1, by norm_num, ?_⟩
    intro i hi
    omega
  | succ n ih =>
    have hpre : ∀ i < n, ∃ δ : ℝ, D (v i) (v (i + 1)) < δ ∧
        ∀ z ∉ U, δ ≤ D (v i) z := by
      intro i hi
      exact hchain i (Nat.lt_succ_of_lt hi)
    obtain ⟨ε, hε, hεchain⟩ := ih hpre
    obtain ⟨δ, hδ, hclear⟩ := hchain n (Nat.lt_succ_self n)
    refine ⟨min ε ((δ - D (v n) (v (n + 1))) / 6),
      lt_min hε (by linarith), ?_⟩
    intro i hi
    by_cases hin : i = n
    · subst i
      refine ⟨δ, ?_, hclear⟩
      have hm := min_le_right ε ((δ - D (v n) (v (n + 1))) / 6)
      linarith
    · have hin' : i < n := by omega
      obtain ⟨δ', hδ', hclear'⟩ := hεchain i hin'
      refine ⟨δ', ?_, hclear'⟩
      have hm := min_le_left ε ((δ - D (v n) (v (n + 1))) / 6)
      linarith

/-- A Euclidean-dense set contains points arbitrarily close in any metric
which induces the Euclidean topology. -/
theorem IsEuclideanLengthMetric.exists_mem_dense_distance_lt
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {S : Set ℂ} (hS : Dense S)
    (x : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ y ∈ S, D x y < ε := by
  have hc : Continuous fun y => D x y := by
    simpa only [hD.symm x] using hD.continuous_left x
  have hopen : IsOpen {y | D x y < ε} := isOpen_lt hc continuous_const
  have hne : {y | D x y < ε}.Nonempty := ⟨x, by simpa only [mem_ofPred_eq, hD.self_eq_zero] using hε⟩
  obtain ⟨y, hy, hy'⟩ := hS.exists_mem_open hopen hne
  exact ⟨y, hy, hy'⟩

/-- Approximate the interior vertices of a finite sequence by a dense set,
while fixing both endpoints. -/
theorem IsEuclideanLengthMetric.exists_dense_vertices
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {S : Set ℂ} (hS : Dense S)
    (v : ℕ → ℂ) (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : ℕ → ℂ, w 0 = v 0 ∧ w n = v n ∧
      (∀ i, i ≠ 0 → i ≠ n → w i ∈ S) ∧ ∀ i, D (v i) (w i) < ε := by
  classical
  choose w hwS hwD using fun i => hD.exists_mem_dense_distance_lt hS (v i) hε
  let w' : ℕ → ℂ := fun i => if i = 0 ∨ i = n then v i else w i
  refine ⟨w', ?_, ?_, ?_, ?_⟩
  · simp only [w', true_or, ↓reduceIte]
  · simp only [w', or_true, ↓reduceIte]
  · intro i hi0 hin
    simpa only [w', hi0, hin, or_self, ↓reduceIte] using hwS i
  · intro i
    by_cases hi : i = 0 ∨ i = n
    · simpa only [w', hi, ↓reduceIte, hD.self_eq_zero] using hε
    · simpa only [w', hi, ↓reduceIte] using hwD i

/-- Finite clearance chains can be perturbed to a dense set at all interior
vertices, while retaining rational boundary clearance and fixing endpoints. -/
theorem IsEuclideanLengthMetric.exists_dense_clearance_chain
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {S U : Set ℂ} (hS : Dense S)
    (v : ℕ → ℂ) (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hchain : ∀ i < n, ∃ δ : ℝ, D (v i) (v (i + 1)) < δ ∧
      ∀ z ∉ U, δ ≤ D (v i) z) :
    ∃ w : ℕ → ℂ, w 0 = v 0 ∧ w n = v n ∧
      (∀ i, i ≠ 0 → i ≠ n → w i ∈ S) ∧ (∀ i, D (v i) (w i) < ε) ∧
      ∀ i < n, ∃ q : ℚ, 0 < q ∧ D (w i) (w (i + 1)) < (q : ℝ) ∧
        ∀ z ∉ U, (q : ℝ) ≤ D (w i) z := by
  obtain ⟨η, hη, hmargin⟩ := finite_chain_boundary_clearance_margin v n hchain
  obtain ⟨w, hw0, hwn, hwS, hwD⟩ := hD.exists_dense_vertices hS v n
    (lt_min hη hε)
  refine ⟨w, hw0, hwn, hwS, ?_, ?_⟩
  · intro i
    exact (hwD i).trans_le (min_le_right _ _)
  · intro i hi
    obtain ⟨δ, hδ, hclear⟩ := hmargin i hi
    have ha : D (v i) (w i) < η := (hwD i).trans_le (min_le_left _ _)
    have hb : D (v (i + 1)) (w (i + 1)) < η :=
      (hwD (i + 1)).trans_le (min_le_left _ _)
    obtain ⟨hshort, hclear'⟩ := hD.boundary_clearance_stable hδ ha hb hclear
    exact exists_rational_boundary_clearance hnonneg hshort hclear'

/-- Perturbing every vertex of a finite chain by at most ε increases its
length by at most 2ε per edge. -/
theorem IsEuclideanLengthMetric.chain_cost_le_of_vertices_near
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) (v w : ℕ → ℂ) (n : ℕ)
    {ε : ℝ} (hε : 0 ≤ ε) (hnear : ∀ i, D (v i) (w i) ≤ ε) :
    (∑ i ∈ Finset.range n, ENNReal.ofReal (D (w i) (w (i + 1)))) ≤
      (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))) +
      ∑ _i ∈ Finset.range n, ENNReal.ofReal (2 * ε) := by
  calc
    (∑ i ∈ Finset.range n, ENNReal.ofReal (D (w i) (w (i + 1)))) ≤
        ∑ i ∈ Finset.range n,
          (ENNReal.ofReal (D (v i) (v (i + 1))) + ENNReal.ofReal (2 * ε)) := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hD.distance_perturb_le (v i) (v (i + 1)) (w i) (w (i + 1))
      have hle : D (w i) (w (i + 1)) ≤ D (v i) (v (i + 1)) + 2 * ε := by
        linarith [hnear i, hnear (i + 1)]
      calc
        ENNReal.ofReal (D (w i) (w (i + 1))) ≤
            ENNReal.ofReal (D (v i) (v (i + 1)) + 2 * ε) := ENNReal.ofReal_le_ofReal hle
        _ = ENNReal.ofReal (D (v i) (v (i + 1))) + ENNReal.ofReal (2 * ε) :=
          ENNReal.ofReal_add (hnonneg _ _) (by positivity)
    _ = (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))) +
        ∑ _i ∈ Finset.range n, ENNReal.ofReal (2 * ε) := Finset.sum_add_distrib

/-- A finite clearance chain can be replaced by one with dense-set interior
vertices, preserving endpoints and changing its cost by at most ε. -/
theorem IsEuclideanLengthMetric.exists_dense_clearance_chain_cost_le
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {S U : Set ℂ} (hS : Dense S)
    (v : ℕ → ℂ) (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hchain : ∀ i < n, ∃ δ : ℝ, D (v i) (v (i + 1)) < δ ∧
      ∀ z ∉ U, δ ≤ D (v i) z) :
    ∃ w : ℕ → ℂ, w 0 = v 0 ∧ w n = v n ∧
      (∀ i, i ≠ 0 → i ≠ n → w i ∈ S) ∧
      (∀ i < n, ∃ q : ℚ, 0 < q ∧ D (w i) (w (i + 1)) < (q : ℝ) ∧
        ∀ z ∉ U, (q : ℝ) ≤ D (w i) z) ∧
      (∑ i ∈ Finset.range n, ENNReal.ofReal (D (w i) (w (i + 1)))) ≤
        (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))) + ENNReal.ofReal ε := by
  let κ : ℝ := ε / (2 * (n + 1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  obtain ⟨w, hw0, hwn, hwS, hwD, hwclear⟩ :=
    hD.exists_dense_clearance_chain hnonneg hS v n hκ hchain
  refine ⟨w, hw0, hwn, hwS, hwclear, ?_⟩
  have hcost := hD.chain_cost_le_of_vertices_near hnonneg v w n hκ.le (fun i => (hwD i).le)
  apply hcost.trans
  gcongr
  have hbound : (n : ℝ) * (2 * κ) ≤ ε := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hfrac : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := (div_le_one₀ hden).2 (by linarith)
    calc
      (n : ℝ) * (2 * κ) = ε * ((n : ℝ) / ((n : ℝ) + 1)) := by
        dsimp [κ]
        field_simp
      _ ≤ ε * 1 := mul_le_mul_of_nonneg_left hfrac hε.le
      _ = ε := mul_one ε
  calc
    (∑ _i ∈ Finset.range n, ENNReal.ofReal (2 * κ)) =
        ENNReal.ofReal (∑ _i ∈ Finset.range n, (2 * κ : ℝ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (by intro i hi; positivity)]
    _ = ENNReal.ofReal ((n : ℝ) * (2 * κ)) := by simp [nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hbound

end HarmonicBalls
