import HarmonicBalls.Defs.LQGMetric
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-! # Subdivided paths and internal metrics of pieces (fp-S11ac, owner z6)

Deterministic part of the punctured metric decoder (`metricDecoder_punctured_ball`). For a length metric `D`
(`IsEuclideanLengthMetric D`), a path `γ` cut at times `0 = u 0 ≤ ⋯ ≤ u N = 1` into pieces
`γ([u i, u (i+1)]) ⊆ U i` satisfies

  `∑ i < N, internalMetric D (U i) (γ (u i)) (γ (u (i+1))) ≤ pathLength D γ`.

The proof uses the variation form of `curveLength` (as in `InternalMetricPaths.lean`), its additivity over adjacent
intervals (`eVariationOn.Icc_add_Icc`), and the reparametrisation inequality `curveLength_reparam_le`.
-/

namespace HarmonicBalls.S11ac

open Set Filter Topology unitInterval
open scoped ENNReal

variable {D : ℂ → ℂ → ℝ}

/-- Points of `ℂ` regarded as a metric space through a length metric `D` (for the variation form of lengths). -/
structure LenPt where
  val : ℂ

/-- The metric on `LenPt` given by a length metric `D`. -/
abbrev lenMetric (hD : IsEuclideanLengthMetric D) : MetricSpace LenPt where
  dist x y := D x.val y.val
  dist_self x := hD.self_eq_zero x.val
  dist_comm x y := hD.symm x.val y.val
  dist_triangle x y z := hD.triangle x.val y.val z.val
  eq_of_dist_eq_zero {x y} h := by
    cases x
    cases y
    exact congrArg LenPt.mk (hD.eq_of_eq_zero _ _ h)

/-- Additivity of `curveLength` over adjacent intervals, read as additivity of a variation. -/
theorem curveLength_add (hD : IsEuclideanLengthMetric D) (p : ℝ → ℂ) {a b c : ℝ} (hab : a ≤ b)
    (hbc : b ≤ c) : curveLength D p a b + curveLength D p b c = curveLength D p a c := by
  let _ := lenMetric hD
  have hcurve : ∀ s t : ℝ, curveLength D p s t = eVariationOn (fun τ => (⟨p τ⟩ : LenPt)) (Icc s t) := by
    intro s t
    simp only [curveLength, eVariationOn, edist_dist]
    rfl
  rw [hcurve, hcurve, hcurve]
  have h := eVariationOn.Icc_add_Icc (fun τ => (⟨p τ⟩ : LenPt)) (s := Icc a c) hab hbc ⟨hab, hbc⟩
  rwa [inter_eq_right.mpr (Icc_subset_Icc le_rfl hbc), inter_eq_right.mpr (Icc_subset_Icc hab le_rfl),
    inter_self] at h

/-- Superadditivity over a finite subdivision. -/
theorem sum_curveLength_le (hD : IsEuclideanLengthMetric D) (p : ℝ → ℂ) (N : ℕ) (u : ℕ → ℝ)
    (hu : Monotone u) :
    ∑ i ∈ Finset.range N, curveLength D p (u i) (u (i + 1)) ≤ curveLength D p (u 0) (u N) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h1 := curveLength_add hD p (hu (Nat.zero_le n)) (hu (Nat.le_succ n))
    calc ∑ i ∈ Finset.range n, curveLength D p (u i) (u (i + 1))
          + curveLength D p (u n) (u (n + 1))
        ≤ curveLength D p (u 0) (u n) + curveLength D p (u n) (u (n + 1)) := by gcongr
      _ = curveLength D p (u 0) (u (n + 1)) := h1

/-- Reparametrisation: a monotone map of `[0,1]` into `[a,b]` gives a curve whose length on `[0,1]` is at most the
length of the original curve on `[a,b]`. -/
theorem curveLength_reparam_le (p r : ℝ → ℂ) {a b : ℝ} (φ : ℝ → ℝ)
    (hφ : MonotoneOn φ (Icc (0 : ℝ) 1)) (hmaps : MapsTo φ (Icc (0 : ℝ) 1) (Icc a b))
    (hpr : ∀ t ∈ Icc (0 : ℝ) 1, r t = p (φ t)) :
    curveLength D r 0 1 ≤ curveLength D p a b := by
  unfold curveLength
  refine iSup_le fun q => ?_
  obtain ⟨n, u, hu, hmem⟩ := q
  have hmon : Monotone (fun i => φ (u i)) := fun i j hij => hφ (hmem i) (hmem j) (hu hij)
  have hmem' : ∀ i, φ (u i) ∈ Icc a b := fun i => hmaps (hmem i)
  calc ∑ i ∈ Finset.range n, ENNReal.ofReal (D (r (u (i + 1))) (r (u i)))
      = ∑ i ∈ Finset.range n, ENNReal.ofReal (D (p (φ (u (i + 1)))) (p (φ (u i)))) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hpr _ (hmem _), hpr _ (hmem _)]
    _ ≤ ⨆ (q : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc a b}),
          ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p (q.2.1 (i + 1))) (p (q.2.1 i))) :=
        le_iSup (fun q : ℕ × {v : ℕ → ℝ // Monotone v ∧ ∀ i, v i ∈ Icc a b} =>
          ∑ i ∈ Finset.range q.1, ENNReal.ofReal (D (p (q.2.1 (i + 1))) (p (q.2.1 i))))
          ⟨n, ⟨fun i => φ (u i), hmon, hmem'⟩⟩

/-- The internal metric of a set `U` between the values of a path on `[a,b] ⊆ [0,1]` is at most the length of the
path on `[a,b]`, provided the path stays in `U` there. -/
theorem internalMetric_le_curveLength {U : Set ℂ} {x y : ℂ} (γ : Path x y)
    {a b : ℝ} (hab : a ≤ b) (hU : ∀ t ∈ Icc a b, γ.extend t ∈ U) :
    internalMetric D U (γ.extend a) (γ.extend b) ≤ curveLength D γ.extend a b := by
  let Q : Path (γ.extend a) (γ.extend b) :=
    { toFun := fun s => γ.extend (a + (s : ℝ) * (b - a))
      continuous_toFun := by
        exact γ.continuous_extend.comp (by fun_prop)
      source' := by simp
      target' := by simp }
  have hQU : ∀ s : I, Q s ∈ U := fun s => by
    apply hU
    have h1 := mul_nonneg s.2.1 (sub_nonneg.2 hab)
    have h2 := mul_le_of_le_one_left (sub_nonneg.2 hab) s.2.2
    exact ⟨by linarith, by linarith⟩
  have hlen : pathLength D Q ≤ curveLength D γ.extend a b := by
    unfold pathLength
    refine curveLength_reparam_le γ.extend Q.extend (fun t => a + t * (b - a)) ?_ ?_ ?_
    · intro s _ t _ hst
      have := mul_le_mul_of_nonneg_right hst (sub_nonneg.2 hab)
      simp only
      linarith
    · intro t ht
      have h1 := mul_nonneg ht.1 (sub_nonneg.2 hab)
      have h2 := mul_le_of_le_one_left (sub_nonneg.2 hab) ht.2
      exact ⟨by simp only; linarith, by simp only; linarith⟩
    · intro t ht
      exact Path.extend_extends' Q ⟨t, ht⟩
  calc internalMetric D U (γ.extend a) (γ.extend b) ≤ pathLength D Q := by
        unfold internalMetric
        exact iInf₂_le Q (fun s => hQU s)
    _ ≤ curveLength D γ.extend a b := hlen

/-- **Chain bound.** A path in `X` cut at `0 = u 0 ≤ ⋯ ≤ u N = 1` into pieces `U i` on which it stays satisfies
`∑ i < N, internalMetric D (U i) (γ (u i)) (γ (u (i+1))) ≤ pathLength D γ`. -/
theorem sum_internalMetric_le_pathLength (hD : IsEuclideanLengthMetric D) {x y : ℂ} (γ : Path x y) (N : ℕ)
    (u : ℕ → ℝ) (hu : Monotone u) (h0 : u 0 = 0) (hN : u N = 1) (U : ℕ → Set ℂ)
    (hU : ∀ i < N, ∀ t ∈ Icc (u i) (u (i + 1)), γ.extend t ∈ U i) :
    ∑ i ∈ Finset.range N, internalMetric D (U i) (γ.extend (u i)) (γ.extend (u (i + 1)))
      ≤ pathLength D γ := by
  calc ∑ i ∈ Finset.range N, internalMetric D (U i) (γ.extend (u i)) (γ.extend (u (i + 1)))
      ≤ ∑ i ∈ Finset.range N, curveLength D γ.extend (u i) (u (i + 1)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hiN : i < N := Finset.mem_range.1 hi
        exact internalMetric_le_curveLength γ (hu (Nat.le_succ i)) (hU i hiN)
    _ ≤ curveLength D γ.extend (u 0) (u N) := sum_curveLength_le hD γ.extend N u hu
    _ = pathLength D γ := by
        rw [h0, hN]
        rfl

end HarmonicBalls.S11ac

#print axioms HarmonicBalls.S11ac.sum_internalMetric_le_pathLength
#print axioms HarmonicBalls.S11ac.curveLength_add
