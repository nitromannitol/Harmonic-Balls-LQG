import HarmonicBalls.Proofs.Sec9.MassOrderedBalls

/-! # Countable nested representatives

A countable family of sets ordered almost everywhere admits nested
representatives after removal of one common measurable null set.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

/-- A countable family ordered almost everywhere by a preorder becomes
pointwise ordered after one common measurable null set is removed. -/
theorem exists_common_null_set_of_ae_order
    {X I : Type*} [MeasurableSpace X] [Countable I] [Preorder I]
    (μ : Measure X) (A : I → Set X)
    (horder : ∀ i j, i ≤ j → μ (A i \ A j) = 0) :
    ∃ N : Set X, MeasurableSet N ∧ μ N = 0 ∧
      ∀ i j, i ≤ j → A i \ N ⊆ A j \ N := by
  have hgood : ∀ᵐ x ∂μ, ∀ i j, i ≤ j → x ∈ A i → x ∈ A j := by
    apply ae_all_iff.2
    intro i
    apply ae_all_iff.2
    intro j
    by_cases hij : i ≤ j
    · have h := horder i j hij
      have hae : ∀ᵐ x ∂μ, x ∉ A i \ A j := measure_eq_zero_iff_ae_notMem.1 h
      filter_upwards [hae] with x hx _ hxi
      by_contra hxj
      exact hx ⟨hxi, hxj⟩
    · exact Filter.Eventually.of_forall fun _ h _ => (hij h).elim
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  refine ⟨N, hNm, hN, ?_⟩
  intro i j hij x hx
  have hxgood : ∀ i j, i ≤ j → x ∈ A i → x ∈ A j := by
    by_contra h
    exact hx.2 (hsub h)
  exact ⟨hxgood i j hij hx.1, hx.2⟩

universe u

/-- On one probability-one event, each countable mass-ordered family of
same-centre subharmonic balls compactly contained in the unit disc has
nested measurable representatives obtained by removing one common null set.
The null set may depend on the family and the realization. -/
theorem ae_countable_subharmonicBalls_have_nested_representatives
    {I : Type*} [Countable I] [Preorder I]
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : I → Set ℂ) (z : ℂ),
      (∀ i, closure (A i) ⊆ ball 0 1 ∧ IsSubharmonicBall (μ ω) (A i) z) →
      (∀ i j, i ≤ j → μ ω (A i) ≤ μ ω (A j)) →
      ∃ N : Set ℂ, MeasurableSet N ∧ μ ω N = 0 ∧
        (∀ i j, i ≤ j → A i \ N ⊆ A j \ N) ∧
        (∀ i, MeasurableSet (A i \ N) ∧
          (μ ω).restrict (A i \ N) = (μ ω).restrict (A i)) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_order_inside_unit_disc hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder
  intro A z hA hmass
  have h := exists_common_null_set_of_ae_order (μ ω) A (by
    intro i j hij
    exact (horder (A i) (A j) z (hA i).1 (hA j).1
      (hA i).2 (hA j).2 (hmass i j hij)).2.2.1)
  obtain ⟨N, hNm, hN, hnested⟩ := h
  refine ⟨N, hNm, hN, hnested, ?_⟩
  intro i
  exact ⟨(hA i).2.1.measurableSet.diff hNm,
    Measure.restrict_congr_set (sdiff_null_ae_eq_self hN)⟩

end HarmonicBalls
