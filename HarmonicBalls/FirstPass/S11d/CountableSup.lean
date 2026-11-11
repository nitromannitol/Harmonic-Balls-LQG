import Mathlib

/-!
# Proposition 11.9, countable suprema for the exterior bound

FIRST-PASS NEW. Deterministic and measure-theoretic tools for the exterior bound
`sup_{u,v ∈ V \ S₂} D_h(u,v; O) ≤ A` (corrected paper, proof of `prop:mass-diam-gen`, lines 3120-3125):
* `le_on_closure_of_continuousOn`: a bound on a set `A` transfers to `closure A` for a continuous `ℝ≥0∞`-valued
  function on `O × O` (the general form of `internalMetric_le_on_closure`, `Core.lean:54`);
* `iSup_eq_countable_dense`: the supremum over `A` equals the supremum over a countable dense subset of `A`;
* `exists_nat_measure_pos_inter_le`: if `M` is measurable and finite almost surely, then some `A ∩ {M ≤ n}` is a
  measurable set of positive measure (`A` measurable with `P A > 0`). This gives the deterministic bound `n` of the
  exterior sup with positive probability, as needed by the Draft statement `SmallMetricDiameterLargeMassStmt`.
-/

namespace HarmonicBalls

open Set MeasureTheory Filter Topology
open scoped ENNReal

/-- Closure extension: a bound `F u v ≤ c` on `A × A` extends to `closure A × closure A` when `F` is continuous on
`O × O` and `closure A ⊆ O`. -/
theorem le_on_closure_of_continuousOn {F : ℂ → ℂ → ℝ≥0∞} {O A : Set ℂ}
    (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (O ×ˢ O)) (hclO : closure A ⊆ O) {c : ℝ≥0∞}
    (h : ∀ u ∈ A, ∀ v ∈ A, F u v ≤ c) :
    ∀ u ∈ closure A, ∀ v ∈ closure A, F u v ≤ c := by
  have hcont : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (closure A ×ˢ closure A) :=
    hF.mono (prod_mono hclO hclO)
  have hclosed : IsClosed ((closure A ×ˢ closure A) ∩
      (fun p : ℂ × ℂ => F p.1 p.2) ⁻¹' Iic c) :=
    hcont.preimage_isClosed_of_isClosed (isClosed_closure.prod isClosed_closure) isClosed_Iic
  have hsub : A ×ˢ A ⊆ (closure A ×ˢ closure A) ∩ (fun p : ℂ × ℂ => F p.1 p.2) ⁻¹' Iic c := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨⟨subset_closure hu, subset_closure hv⟩, h u hu v hv⟩
  have hcl := hclosed.closure_subset_iff.mpr hsub
  rw [closure_prod_eq] at hcl
  intro u hu v hv
  exact (hcl (show (u, v) ∈ closure A ×ˢ closure A from ⟨hu, hv⟩)).2

/-- The supremum of a function continuous on `O × O` over `A` equals its supremum over a countable subset `Q ⊆ A`
with `A ⊆ closure Q` (here `Q` is a countable dense subset of the open set `V \ S₂`). -/
theorem iSup_eq_countable_dense {F : ℂ → ℂ → ℝ≥0∞} {O A Q : Set ℂ}
    (hF : ContinuousOn (fun p : ℂ × ℂ => F p.1 p.2) (O ×ˢ O)) (hAO : closure A ⊆ O)
    (hQA : Q ⊆ A) (hAQ : A ⊆ closure Q) :
    (⨆ u ∈ A, ⨆ v ∈ A, F u v) = ⨆ q ∈ Q, ⨆ q' ∈ Q, F q q' := by
  apply le_antisymm
  · refine iSup₂_le fun u hu => iSup₂_le fun v hv => ?_
    have hclQ : closure Q ⊆ O := (closure_mono hQA).trans hAO
    refine le_on_closure_of_continuousOn hF hclQ
      (c := ⨆ q ∈ Q, ⨆ q' ∈ Q, F q q') ?_ u (hAQ hu) v (hAQ hv)
    intro q hq q' hq'
    exact le_iSup₂_of_le q hq (le_iSup₂_of_le q' hq' le_rfl)
  · refine iSup₂_le fun q hq => iSup₂_le fun q' hq' => ?_
    exact le_iSup₂_of_le q (hQA hq) (le_iSup₂_of_le q' (hQA hq') le_rfl)

/-- If `M` is measurable and finite almost surely, and `A` is measurable with `P A > 0`, then for some `n : ℕ` the set
`A ∩ {M ≤ n}` is measurable with positive measure. -/
theorem exists_nat_measurable_pos_inter_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Set Ω}
    (hA : MeasurableSet A) (hAp : 0 < P A) {M : Ω → ℝ≥0∞} (hM : Measurable M)
    (hfin : ∀ᵐ ω ∂P, M ω < ⊤) :
    ∃ n : ℕ, MeasurableSet (A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) ∧ 0 < P (A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) := by
  have hmeas : ∀ n : ℕ, MeasurableSet (A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) := fun n =>
    hA.inter (measurableSet_le hM measurable_const)
  by_contra hcon
  have hcon' : ∀ n : ℕ, P (A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) ≤ 0 := fun n =>
    not_lt.mp (fun h => hcon ⟨n, hmeas n, h⟩)
  have hnull : ∀ n : ℕ, P (A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) = 0 := fun n =>
    nonpos_iff_eq_zero.mp (hcon' n)
  have hU : P (⋃ n : ℕ, A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) = 0 := measure_iUnion_null hnull
  have hsub : A ⊆ (⋃ n : ℕ, A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) ∪ {ω | ¬ M ω < ⊤} := by
    intro ω hω
    by_cases h : M ω < ⊤
    · obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt h.ne
      exact Or.inl (mem_iUnion.mpr ⟨n, hω, hn.le⟩)
    · exact Or.inr h
  have hexc : P {ω | ¬ M ω < ⊤} = 0 := ae_iff.mp hfin
  have hle : P A ≤ 0 := by
    calc P A ≤ P ((⋃ n : ℕ, A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) ∪ {ω | ¬ M ω < ⊤}) := measure_mono hsub
      _ ≤ P (⋃ n : ℕ, A ∩ {ω | M ω ≤ (n : ℝ≥0∞)}) + P {ω | ¬ M ω < ⊤} := measure_union_le _ _
      _ = 0 := by rw [hU, hexc, add_zero]
  exact absurd hAp (not_lt.mpr hle)

end HarmonicBalls
