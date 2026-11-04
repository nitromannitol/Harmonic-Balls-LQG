import HarmonicBalls.Steps.Sec11.BoundaryClearance

/-! # Chains of edges with boundary clearance -/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- It is measurable whether all edges of a fixed finite chain have
rational boundary clearance. -/
theorem measurableSet_chain_with_rational_boundary_clearance
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} (U : Set ℂ)
    (v : ℕ → ℂ) (n : ℕ) (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hcont : ∀ ω x, Continuous fun y => D ω x y) :
    MeasurableSet {ω | ∀ i < n, ∃ δ : ℚ, 0 < δ ∧
      D ω (v i) (v (i + 1)) < (δ : ℝ) ∧ ∀ z ∉ U, (δ : ℝ) ≤ D ω (v i) z} := by
  have heq : {ω | ∀ i < n, ∃ δ : ℚ, 0 < δ ∧
      D ω (v i) (v (i + 1)) < (δ : ℝ) ∧ ∀ z ∉ U, (δ : ℝ) ≤ D ω (v i) z} =
      ⋂ i : ℕ, ⋂ (_ : i < n), {ω | ∃ δ : ℚ, 0 < δ ∧
        D ω (v i) (v (i + 1)) < (δ : ℝ) ∧ ∀ z ∉ U, (δ : ℝ) ≤ D ω (v i) z} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter]
  rw [heq]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_edge_with_rational_boundary_clearance U (v i) (v (i + 1)) (hD _) (fun ω => hcont ω _)

open scoped Classical in
/-- The cost of a fixed finite chain, set to infinity when it lacks rational
boundary clearance, is measurable. -/
theorem measurable_boundary_clearance_chain_cost
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ} (U : Set ℂ)
    (v : ℕ → ℂ) (n : ℕ) (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hcont : ∀ ω x, Continuous fun y => D ω x y) :
    Measurable fun ω => if ∀ i < n, ∃ δ : ℚ, 0 < δ ∧
      D ω (v i) (v (i + 1)) < (δ : ℝ) ∧ ∀ z ∉ U, (δ : ℝ) ≤ D ω (v i) z
      then ∑ i ∈ Finset.range n, ENNReal.ofReal (D ω (v i) (v (i + 1))) else ∞ := by
  classical
  exact Measurable.ite (measurableSet_chain_with_rational_boundary_clearance U v n hD hcont)
    (Finset.measurable_sum _ (fun i _ => (hD _ _).ennreal_ofReal)) measurable_const

open scoped Classical in
/-- The infimum of the costs of a countable family of fixed finite chains is
measurable. -/
theorem measurable_iInf_boundary_clearance_chain_cost
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {D : Ω → ℂ → ℂ → ℝ} (U : Set ℂ)
    (v : ι → ℕ → ℂ) (n : ι → ℕ) (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hcont : ∀ ω x, Continuous fun y => D ω x y) :
    Measurable fun ω => ⨅ k : ι, if ∀ i < n k, ∃ δ : ℚ, 0 < δ ∧
      D ω (v k i) (v k (i + 1)) < (δ : ℝ) ∧ ∀ z ∉ U, (δ : ℝ) ≤ D ω (v k i) z
      then ∑ i ∈ Finset.range (n k), ENNReal.ofReal (D ω (v k i) (v k (i + 1)))
      else ∞ := by
  have hm := Measurable.iInf (fun k : ι =>
    measurable_boundary_clearance_chain_cost U (v k) (n k) hD hcont)
  convert hm using 1

/-- The internal distance between the endpoints of a finite chain is bounded
by the sum of the ambient distances along edges with boundary clearance. -/
theorem IsEuclideanLengthMetric.internalMetric_le_sum_of_boundary_clearance
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    (v : ℕ → ℂ) (hv : v 0 ∈ U) (n : ℕ)
    (hchain : ∀ i < n, ∃ δ : ℝ, D (v i) (v (i + 1)) < δ ∧
      ∀ z ∉ U, δ ≤ D (v i) z) :
    internalMetric D U (v 0) (v n) ≤
      ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) := by
  induction n with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty] using
      (hD.internalMetric_self_of_mem_open hnonneg hU hv).le
  | succ n ih =>
    have hpre : ∀ i < n, ∃ δ : ℝ, D (v i) (v (i + 1)) < δ ∧
        ∀ z ∉ U, δ ≤ D (v i) z := by
      intro i hi
      exact hchain i (Nat.lt_succ_of_lt hi)
    obtain ⟨δ, hδ, hclear⟩ := hchain n (Nat.lt_succ_self n)
    rw [Finset.sum_range_succ]
    calc
      internalMetric D U (v 0) (v (n + 1)) ≤
          internalMetric D U (v 0) (v n) + internalMetric D U (v n) (v (n + 1)) :=
        hD.internalMetric_triangle U _ _ _
      _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))) +
          ENNReal.ofReal (D (v n) (v (n + 1))) := by
        gcongr
        · exact ih hpre
        · exact (hD.internalMetric_eq_of_boundary_clearance hnonneg hclear hδ).le

open scoped Classical in
/-- Internal distance is bounded above by the cost of any fixed chain; an
inadmissible chain has infinite cost. -/
theorem IsEuclideanLengthMetric.internalMetric_le_boundary_clearance_chain_cost
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U)
    (v : ℕ → ℂ) (hv : v 0 ∈ U) (n : ℕ) :
    internalMetric D U (v 0) (v n) ≤
      if ∀ i < n, ∃ δ : ℚ, 0 < δ ∧ D (v i) (v (i + 1)) < (δ : ℝ) ∧
        ∀ z ∉ U, (δ : ℝ) ≤ D (v i) z
      then ∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1))) else ∞ := by
  split_ifs with h
  · apply hD.internalMetric_le_sum_of_boundary_clearance hnonneg hU v hv n
    intro i hi
    obtain ⟨δ, _, hδ, hclear⟩ := h i hi
    exact ⟨δ, hδ, hclear⟩
  · exact le_top

open scoped Classical in
/-- Internal distance is bounded above by the infimum of clearance-chain costs
among chains with the prescribed endpoints. -/
theorem IsEuclideanLengthMetric.internalMetric_le_iInf_boundary_clearance_chain_cost
    {ι : Type*} {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {U : Set ℂ} (hU : IsOpen U) {x y : ℂ}
    (hx : x ∈ U) (v : ι → ℕ → ℂ) (n : ι → ℕ)
    (hstart : ∀ k, v k 0 = x) (hend : ∀ k, v k (n k) = y) :
    internalMetric D U x y ≤ ⨅ k : ι,
      if ∀ i < n k, ∃ δ : ℚ, 0 < δ ∧ D (v k i) (v k (i + 1)) < (δ : ℝ) ∧
        ∀ z ∉ U, (δ : ℝ) ≤ D (v k i) z
      then ∑ i ∈ Finset.range (n k), ENNReal.ofReal (D (v k i) (v k (i + 1))) else ∞ := by
  apply le_iInf
  intro k
  have hm := hD.internalMetric_le_boundary_clearance_chain_cost hnonneg hU (v k)
    (by simpa only [hstart k] using hx) (n k)
  simpa only [hstart k, hend k] using hm

end HarmonicBalls
