import HarmonicBalls.Steps.Sec11.CountableClearanceChains

/-! # Clearance chains tested against a countable set

The dense-chain formula `internalMetric_eq_denseClearanceChainInf` (`Steps/Sec11/CountableClearanceChains.lean`)
computes the internal metric `D(x, y; U)` of a Euclidean length metric on an open set `U` as an infimum of chain costs,
where each edge must have a rational boundary clearance `δ ≤ D(vᵢ, z)` for all `z ∉ U`. That clearance condition
quantifies over the uncountable set `Uᶜ`, so its measurability as a function of `D` uses the continuity of `D`.

Here the clearance is tested only against a countable set `C ⊆ Uᶜ` which is dense in `Uᶜ`
(`countableClearanceChainInf`). This functional is measurable for every pointwise measurable family of
functions `ℂ → ℂ → ℝ`, without any continuity (`measurable_countableClearanceChainInf`), and it agrees with the
dense-chain infimum whenever `D` is continuous in its second variable, hence with the internal metric whenever `D`
is a Euclidean length metric (`IsEuclideanLengthMetric.internalMetric_eq_countableClearanceChainInf`). It serves as
a single measurable decoder of internal metrics on the whole space of functions `ℂ → ℂ → ℝ`.
-/

namespace HarmonicBalls

open Set MeasureTheory
open scoped ENNReal

/-- Every set `U ⊆ ℂ` has a countable subset `C` of its complement which is dense in the complement. -/
theorem exists_countable_dense_subset_compl (U : Set ℂ) : ∃ C ⊆ Uᶜ, C.Countable ∧ Uᶜ ⊆ closure C :=
  (TopologicalSpace.IsSeparable.of_separableSpace Uᶜ).exists_countable_dense_subset

open scoped Classical in
/-- Cost of a dense chain whose edges must have a rational clearance `δ` from the points of `C`: the sum of the
`D`-lengths of its edges, or `∞` if some edge `(vᵢ, vᵢ₊₁)` has no rational `δ > 0` with `D(vᵢ, vᵢ₊₁) < δ ≤ D(vᵢ, z)`
for all `z ∈ C`. -/
noncomputable def countableClearanceChainCost {S : Set ℂ} (C : Set ℂ) (D : ℂ → ℂ → ℝ)
    (x y : ℂ) (k : Σ n : ℕ, Fin n → S) : ℝ≥0∞ :=
  if ∀ i < k.1 + 1, ∃ δ : ℚ, 0 < δ ∧
      D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1)) < (δ : ℝ) ∧
      ∀ z ∈ C, (δ : ℝ) ≤ D (denseChainVertex x y k i) z
  then ∑ i ∈ Finset.range (k.1 + 1),
    ENNReal.ofReal (D (denseChainVertex x y k i) (denseChainVertex x y k (i + 1))) else ∞

/-- Infimum of the costs of the dense chains from `x` to `y` with interior vertices in `S`, the boundary clearance
being tested against the points of `C`. -/
noncomputable def countableClearanceChainInf (S C : Set ℂ) (D : ℂ → ℂ → ℝ) (x y : ℂ) : ℝ≥0∞ :=
  ⨅ k : Σ n : ℕ, Fin n → S, countableClearanceChainCost C D x y k

/-- The set of parameters at which a fixed finite chain has rational clearance from a countable set `C` on every
edge is measurable, for a pointwise measurable family of functions. -/
theorem measurableSet_chain_countable_clearance {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    {C : Set ℂ} (hC : C.Countable) (hD : ∀ a b, Measurable fun ω => D ω a b) (v : ℕ → ℂ) (n : ℕ) :
    MeasurableSet {ω | ∀ i < n, ∃ δ : ℚ, 0 < δ ∧ D ω (v i) (v (i + 1)) < (δ : ℝ) ∧
      ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z} := by
  have := hC.to_subtype
  have h1 : ∀ (i : ℕ) (δ : ℚ), MeasurableSet {ω | ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z} := by
    intro i δ
    have he : {ω | ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z} = ⋂ z : C, {ω | (δ : ℝ) ≤ D ω (v i) z} := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iInter fun z => measurableSet_le measurable_const (hD _ _)
  have h2 : ∀ i : ℕ, MeasurableSet {ω | ∃ δ : ℚ, 0 < δ ∧ D ω (v i) (v (i + 1)) < (δ : ℝ) ∧
      ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z} := by
    intro i
    have he : {ω | ∃ δ : ℚ, 0 < δ ∧ D ω (v i) (v (i + 1)) < (δ : ℝ) ∧ ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z} =
        ⋃ δ : ℚ, ({_ω | 0 < δ} ∩ ({ω | D ω (v i) (v (i + 1)) < (δ : ℝ)} ∩
          {ω | ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z})) := by
      ext ω
      simp
    rw [he]
    exact MeasurableSet.iUnion fun δ =>
      (MeasurableSet.const _).inter ((measurableSet_lt (hD _ _) measurable_const).inter (h1 i δ))
  have he : {ω | ∀ i < n, ∃ δ : ℚ, 0 < δ ∧ D ω (v i) (v (i + 1)) < (δ : ℝ) ∧
      ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z} = ⋂ i ∈ Finset.range n, {ω | ∃ δ : ℚ, 0 < δ ∧
        D ω (v i) (v (i + 1)) < (δ : ℝ) ∧ ∀ z ∈ C, (δ : ℝ) ≤ D ω (v i) z} := by
    ext ω
    simp
  rw [he]
  exact Finset.measurableSet_biInter _ fun i _ => h2 i

/-- The countable-clearance chain infimum is measurable for every pointwise measurable family of functions
`ℂ → ℂ → ℝ`, when `S` and `C` are countable; no continuity is needed. -/
theorem measurable_countableClearanceChainInf {Ω : Type*} [MeasurableSpace Ω] {D : Ω → ℂ → ℂ → ℝ}
    {S C : Set ℂ} [Countable S] (hC : C.Countable) (x y : ℂ)
    (hD : ∀ a b, Measurable fun ω => D ω a b) :
    Measurable fun ω => countableClearanceChainInf S C (D ω) x y := by
  classical
  refine Measurable.iInf fun k => ?_
  exact Measurable.ite (measurableSet_chain_countable_clearance hC hD (denseChainVertex x y k) (k.1 + 1))
    (Finset.measurable_sum _ fun i _ => (hD _ _).ennreal_ofReal) measurable_const

/-- For `D` continuous in its second variable and `C ⊆ Uᶜ` dense in `Uᶜ`, a rational clearance from the points of
`C` is a clearance from all of `Uᶜ`, so the countable-clearance chain infimum is the dense-chain infimum. -/
theorem countableClearanceChainInf_eq_denseClearanceChainInf {D : ℂ → ℂ → ℝ}
    (hcont : ∀ a, Continuous fun b => D a b) {S C U : Set ℂ} (hCU : C ⊆ Uᶜ) (hUC : Uᶜ ⊆ closure C)
    (x y : ℂ) : countableClearanceChainInf S C D x y = denseClearanceChainInf S U D x y := by
  have key : ∀ (a : ℂ) (δ : ℝ), (∀ z ∈ C, δ ≤ D a z) ↔ ∀ z ∉ U, δ ≤ D a z := by
    intro a δ
    constructor
    · intro h z hz
      have hcl : IsClosed {w | δ ≤ D a w} := isClosed_le continuous_const (hcont a)
      exact hcl.closure_subset_iff.2 (fun w hw => h w hw) (hUC hz)
    · intro h z hz
      exact h z (hCU hz)
  unfold countableClearanceChainInf denseClearanceChainInf
  refine iInf_congr fun k => ?_
  unfold countableClearanceChainCost denseClearanceChainCost
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (fun i hi => (h1 i hi).imp fun δ hδ => ⟨hδ.1, hδ.2.1, (key _ _).1 hδ.2.2⟩) h2
  · exact absurd (fun i hi => (h2 i hi).imp fun δ hδ => ⟨hδ.1, hδ.2.1, (key _ _).2 hδ.2.2⟩) h1
  · rfl

/-- **Countable-clearance chain formula.** For a Euclidean length metric `D`, an open set `U`, a dense set `S` and a set
`C ⊆ Uᶜ` dense in `Uᶜ`, the internal metric `D(x, y; U)` (`x ∈ U`) is the countable-clearance
chain infimum. -/
theorem IsEuclideanLengthMetric.internalMetric_eq_countableClearanceChainInf {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {S C U : Set ℂ} (hS : Dense S) (hU : IsOpen U) (hCU : C ⊆ Uᶜ)
    (hUC : Uᶜ ⊆ closure C) {x : ℂ} (hx : x ∈ U) (y : ℂ) :
    internalMetric D U x y = countableClearanceChainInf S C D x y := by
  have hnonneg : ∀ a b, 0 ≤ D a b := by
    intro a b
    have h := hD.triangle a b a
    rw [hD.self_eq_zero, hD.symm b a] at h
    linarith
  have hcont : ∀ a, Continuous fun b => D a b := fun a => by
    simpa only [hD.symm a] using hD.continuous_left a
  rw [countableClearanceChainInf_eq_denseClearanceChainInf hcont hCU hUC]
  exact hD.internalMetric_eq_denseClearanceChainInf hnonneg hS hU hx

end HarmonicBalls
