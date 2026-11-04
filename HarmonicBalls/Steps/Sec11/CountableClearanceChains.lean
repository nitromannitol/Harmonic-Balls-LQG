import HarmonicBalls.Steps.Sec11.PathClearancePartition

/-! # A countable family of clearance chains -/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- Vertices of a finite chain whose interior vertices belong to `S`. -/
def denseChainVertex {S : Set ℂ} (x y : ℂ) (k : Σ n : ℕ, Fin n → S) (i : ℕ) : ℂ :=
  if h0 : i = 0 then x else if h : i ≤ k.1 then (k.2 ⟨i - 1, by omega⟩ : ℂ) else y

/-- The first vertex of a dense chain is its prescribed starting point. -/
theorem denseChainVertex_start {S : Set ℂ} (x y : ℂ) (k : Σ n : ℕ, Fin n → S) :
    denseChainVertex x y k 0 = x := by simp [denseChainVertex]

/-- The last vertex of a dense chain is its prescribed endpoint. -/
theorem denseChainVertex_end {S : Set ℂ} (x y : ℂ) (k : Σ n : ℕ, Fin n → S) :
    denseChainVertex x y k (k.1 + 1) = y := by
  simp [denseChainVertex]

/-- Every finite sequence with interior vertices in `S` is represented by a
dense chain. -/
theorem exists_denseChainVertex_representation {S : Set ℂ} (w : ℕ → ℂ) (n : ℕ)
    (hn : 0 < n) (hwS : ∀ i, i ≠ 0 → i ≠ n → w i ∈ S) :
    ∃ k : Σ m : ℕ, Fin m → S, k.1 + 1 = n ∧
      ∀ i ≤ n, denseChainVertex (w 0) (w n) k i = w i := by
  cases n with
  | zero => omega
  | succ n =>
    let f : Fin n → S := fun i => ⟨w (i.1 + 1), hwS (i.1 + 1) (by omega) (by omega)⟩
    let k : Σ m : ℕ, Fin m → S := ⟨n, f⟩
    refine ⟨k, rfl, ?_⟩
    intro i hi
    by_cases hi0 : i = 0
    · subst i
      exact denseChainVertex_start _ _ _
    · by_cases hin : i ≤ n
      · have hi' : i - 1 + 1 = i := Nat.sub_add_cancel (by omega)
        simp only [denseChainVertex, hi0, k, hin, dite_true, f]
        exact congrArg w hi'
      · have hi' : i = n + 1 := by omega
        subst i
        exact denseChainVertex_end _ _ _

open scoped Classical in
/-- Cost of a dense chain, with value infinity if any edge lacks rational
boundary clearance. -/
noncomputable def denseClearanceChainCost {S U : Set ℂ} (D : ℂ → ℂ → ℝ)
    (x y : ℂ) (k : Σ n : ℕ, Fin n → S) : ℝ≥0∞ :=
  if ∀ i < k.1 + 1, ∃ δ : ℚ, 0 < δ ∧
      D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ) ∧
      ∀ z ∉ U, (δ : ℝ) ≤ D (denseChainVertex x y k i) z
  then ∑ i ∈ Finset.range (k.1 + 1),
    ENNReal.ofReal (D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1))) else ∞

/-- Infimum of clearance-chain costs with interior vertices in `S`. -/
noncomputable def denseClearanceChainInf (S U : Set ℂ) (D : ℂ → ℂ → ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ k : Σ n : ℕ, Fin n → S, denseClearanceChainCost (U := U) D x y k

/-- The dense-chain infimum is measurable for a pointwise measurable family
of continuous distance functions, when the dense set is countable. -/
theorem measurable_denseClearanceChainInf
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    {S U : Set ℂ} [Countable S] (x y : ℂ)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hcont : ∀ ω x, Continuous fun y => D ω x y) :
    Measurable fun ω => denseClearanceChainInf S U (D ω) x y := by
  simpa only [denseClearanceChainInf, denseClearanceChainCost] using
    measurable_iInf_boundary_clearance_chain_cost U (denseChainVertex x y)
      (fun k => k.1 + 1) hD hcont

/-- The dense-chain infimum dominates the internal metric. -/
theorem IsEuclideanLengthMetric.internalMetric_le_denseClearanceChainInf
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {S U : Set ℂ} (hU : IsOpen U)
    {x y : ℂ} (hx : x ∈ U) : internalMetric D U x y ≤ denseClearanceChainInf S U D x y := by
  simpa only [denseClearanceChainInf, denseClearanceChainCost] using
    hD.internalMetric_le_iInf_boundary_clearance_chain_cost hnonneg hU hx
      (denseChainVertex x y) (fun k => k.1 + 1)
      (denseChainVertex_start x y) (denseChainVertex_end x y)

/-- A dense-chain infimum is bounded by the length of every path inside the
open set. -/
theorem IsEuclideanLengthMetric.denseClearanceChainInf_le_pathLength
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {S U : Set ℂ} (hS : Dense S) (hU : IsOpen U)
    {x y : ℂ} (p : Path x y) (hp : ∀ t, p t ∈ U) :
    denseClearanceChainInf S U D x y ≤ pathLength D p := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  obtain ⟨n, v, hn, hv0, hvn, hclear, hcost⟩ := hD.exists_clearance_chain_of_path hU p hp
  obtain ⟨w, hw0, hwn, hwS, hwclear, hwcost⟩ :=
    hD.exists_dense_clearance_chain_cost_le hnonneg hS v n hεr hclear
  obtain ⟨k, hk, hkw⟩ := exists_denseChainVertex_representation w n hn hwS
  have hx : w 0 = x := hw0.trans hv0
  have hy : w n = y := hwn.trans hvn
  have hrepr (i : ℕ) (hi : i ≤ n) : denseChainVertex x y k i = w i := by
    simpa only [hx, hy] using hkw i hi
  have hsafe : ∀ i < k.1 + 1, ∃ q : ℚ, 0 < q ∧
      D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (q : ℝ) ∧
      ∀ z ∉ U, (q : ℝ) ≤ D (denseChainVertex x y k i) z := by
    intro i hi
    rw [hk] at hi
    simpa only [hrepr i hi.le, hrepr (i + 1) (Nat.succ_le_of_lt hi)] using hwclear i hi
  have hsum : (∑ i ∈ Finset.range (k.1 + 1), ENNReal.ofReal
      (D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)))) =
      ∑ i ∈ Finset.range n, ENNReal.ofReal (D (w i) (w (i + 1))) := by
    rw [hk]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [hrepr i hi'.le, hrepr (i + 1) (Nat.succ_le_of_lt hi')]
  have hkcost : denseClearanceChainCost (U := U) D x y k =
      ∑ i ∈ Finset.range n, ENNReal.ofReal (D (w i) (w (i + 1))) := by
    classical
    unfold denseClearanceChainCost
    rw [ite_eq_left hsafe]
    exact hsum
  calc
    denseClearanceChainInf S U D x y ≤ denseClearanceChainCost (U := U) D x y k := iInf_le _ k
    _ = ∑ i ∈ Finset.range n, ENNReal.ofReal (D (w i) (w (i + 1))) := hkcost
    _ ≤ (∑ i ∈ Finset.range n, ENNReal.ofReal (D (v i) (v (i + 1)))) +
        ENNReal.ofReal (ε : ℝ) := hwcost
    _ ≤ pathLength D p + ε := by
      simpa only [ENNReal.ofReal_coe_nnreal] using (add_le_add hcost (le_refl (ε : ℝ≥0∞)))

/-- Internal distance on an open set equals the infimum of the costs of dense
clearance chains. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_denseClearanceChainInf
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hnonneg : ∀ x y, 0 ≤ D x y) {S U : Set ℂ} (hS : Dense S) (hU : IsOpen U)
    {x y : ℂ} (hx : x ∈ U) : internalMetric D U x y = denseClearanceChainInf S U D x y := by
  apply le_antisymm (hD.internalMetric_le_denseClearanceChainInf hnonneg hU hx)
  change denseClearanceChainInf S U D x y ≤ ⨅ (p : Path x y) (_ : ∀ t, p t ∈ U), pathLength D p
  exact le_iInf fun p => le_iInf fun hp => hD.denseClearanceChainInf_le_pathLength hnonneg hS hU p hp

/-- Internal distance in an open set is measurable for a pointwise
measurable family of Euclidean length metrics. -/
theorem measurable_internalMetric_of_lengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) (y : ℂ)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ ω, IsEuclideanLengthMetric (D ω)) :
    Measurable fun ω => internalMetric (D ω) U x y := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable S := hSc.to_subtype
  have hnonneg (ω : Ω) (a b : ℂ) : 0 ≤ D ω a b := by
    have h := (hmetric ω).triangle a b a
    rw [(hmetric ω).self_eq_zero, (hmetric ω).symm b a] at h
    linarith
  have hcont (ω : Ω) (a : ℂ) : Continuous fun b => D ω a b := by
    simpa only [(hmetric ω).symm a] using (hmetric ω).continuous_left a
  have hm := measurable_denseClearanceChainInf (S := S) (U := U) x y hD hcont
  convert hm using 1
  ext ω
  exact (hmetric ω).internalMetric_eq_denseClearanceChainInf (hnonneg ω) hSd hU hx

/-- A pointwise measurable random distance which is almost surely a Euclidean
length metric has a pointwise measurable modification that is a Euclidean
length metric everywhere. -/
theorem exists_measurable_lengthMetric_modification
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    ∃ D' : Ω → ℂ → ℂ → ℝ, (∀ x y, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsEuclideanLengthMetric (D' ω)) ∧ ∀ᵐ ω ∂P, D' ω = D ω := by
  classical
  let H : Set Ω := {ω | IsEuclideanLengthMetric (D ω)}
  have hH : NullMeasurableSet H P := by
    apply (nullMeasurableSet_univ (μ := P)).congr
    filter_upwards [hmetric] with ω hω
    simp only [mem_univ, H, mem_ofPred_eq, hω]
  obtain ⟨G, hsub, hG, hGeq⟩ := hH.exists_measurable_subset_ae_eq
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    filter_upwards [hGeq, hmetric] with ω heq hω
    exact Eq.mpr heq hω
  let D' : Ω → ℂ → ℂ → ℝ := fun ω x y => if ω ∈ G then D ω x y else dist x y
  have hD' : ∀ x y, Measurable fun ω => D' ω x y := by
    intro x y
    exact Measurable.ite hG (hD x y) measurable_const
  have hmetric' : ∀ ω, IsEuclideanLengthMetric (D' ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · have h := hsub hω
      change IsEuclideanLengthMetric (D ω) at h
      simpa only [D', hω, ↓reduceIte] using h
    · simpa only [D', hω, ↓reduceIte] using isEuclideanLengthMetric_dist
  refine ⟨D', hD', hmetric', ?_⟩
  filter_upwards [hGae] with ω hω
  funext x y
  simp only [D', hω, ↓reduceIte]

/-- Internal distance is almost-everywhere measurable when the random distance
is pointwise measurable and almost surely a Euclidean length metric. -/
theorem aemeasurable_internalMetric_of_ae_lengthMetric
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    {U : Set ℂ} (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) (y : ℂ)
    (hD : ∀ x y, Measurable fun ω => D ω x y)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    AEMeasurable (fun ω => internalMetric (D ω) U x y) P := by
  obtain ⟨D', hD', hmetric', hEq⟩ := exists_measurable_lengthMetric_modification hD hmetric
  have hm := (measurable_internalMetric_of_lengthMetric hU hx y hD' hmetric').aemeasurable (μ := P)
  apply hm.congr
  filter_upwards [hEq] with ω hω
  rw [hω]

end HarmonicBalls
