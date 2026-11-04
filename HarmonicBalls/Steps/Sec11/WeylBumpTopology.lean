import HarmonicBalls.Steps.Sec11.WeylScalingOrder

/-! # Topology of a bounded nonpositive Weyl shift

A global lower bound on the bump gives a two-sided comparison with the
original metric. The result establishes finiteness, separation and the
Euclidean topology, independently of the length and inverse-Weyl properties.
-/

namespace HarmonicBalls

open Set
open scoped ENNReal

/-- A nonpositive weight bounded below gives a finite Weyl scaling with a
real representative bounded between two positive multiples of the metric. -/
theorem weylScaling_negative_bump_real_bounds
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ}
    (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hl : ∀ z, c ≤ f z)
    (hu : ∀ z, f z ≤ 0)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y))
    (x y : ℂ) :
    weylScaling D ξ f x y < ∞ ∧
    Real.exp (ξ * c) * D x y ≤ (weylScaling D ξ f x y).toReal ∧
    (weylScaling D ξ f x y).toReal ≤ D x y := by
  have hnonneg : 0 ≤ D x y := by
    have h := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at h
    linarith
  have hb := weylScaling_negative_bump_bounds D hξ (0 : ℂ → ℝ) f hl hu x y
  simp only [Pi.zero_apply, zero_add, hzero x y] at hb
  have hfinite : weylScaling D ξ f x y < ∞ :=
    lt_of_le_of_lt hb.2 ENNReal.ofReal_lt_top
  have hleft := (ENNReal.toReal_le_toReal
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hfinite.ne).2 hb.1
  have hright := (ENNReal.toReal_le_toReal hfinite.ne ENNReal.ofReal_ne_top).2 hb.2
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _),
    ENNReal.toReal_ofReal hnonneg] at hleft hright
  exact ⟨hfinite, hleft, hright⟩

/-- A bounded nonpositive Weyl shift separates points, vanishes on the
diagonal, and induces the original Euclidean topology. -/
theorem IsEuclideanLengthMetric.weylScaling_negative_bump_topology
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ c : ℝ}
    (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hl : ∀ z, c ≤ f z)
    (hu : ∀ z, f z ≤ 0)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y)) :
    let E : ℂ → ℂ → ℝ := fun x y => (weylScaling D ξ f x y).toReal
    (∀ x, E x x = 0) ∧ (∀ x y, E x y = 0 → x = y) ∧
    (∀ U : Set ℂ, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, E x y < ε → y ∈ U) := by
  dsimp only
  have hb := weylScaling_negative_bump_real_bounds hD hξ f hl hu hzero
  have hk : 0 < Real.exp (ξ * c) := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have h := (hb x x).2.2
    rw [hD.self_eq_zero] at h
    exact le_antisymm h ENNReal.toReal_nonneg
  · intro x y he
    apply hD.eq_of_eq_zero x y
    have hnonneg : 0 ≤ D x y := by
      have ht := hD.triangle x y x
      rw [hD.self_eq_zero, hD.symm y x] at ht
      linarith
    have h := (hb x y).2.1
    rw [he] at h
    nlinarith
  · intro U
    rw [hD.isOpen_iff U]
    constructor
    · intro h x hx
      obtain ⟨ε, hε, hεx⟩ := h x hx
      refine ⟨Real.exp (ξ * c) * ε, mul_pos hk hε, ?_⟩
      intro y hy
      apply hεx y
      have h := (hb x y).2.1
      nlinarith
    · intro h x hx
      obtain ⟨ε, hε, hεx⟩ := h x hx
      refine ⟨ε, hε, ?_⟩
      intro y hy
      exact hεx y (lt_of_le_of_lt (hb x y).2.2 hy)

/-- A continuous compactly supported real function is bounded below. -/
theorem exists_lower_bound_of_continuous_compactSupport (f : ℂ → ℝ)
    (hf : Continuous f) (hc : HasCompactSupport f) : ∃ c : ℝ, ∀ z, c ≤ f z := by
  obtain ⟨c, hc⟩ := (IsCompact.bddBelow_image hc hf.continuousOn)
  refine ⟨min c 0, ?_⟩
  intro z
  by_cases hz : z ∈ tsupport f
  · exact (min_le_left c 0).trans (hc ⟨z, hz, rfl⟩)
  · have hzero : f z = 0 := by
      by_contra hne
      exact hz (subset_closure hne)
    rw [hzero]
    exact min_le_right c 0

/-- Continuous compactly supported nonpositive weights preserve point
separation and the Euclidean topology of the metric. -/
theorem IsEuclideanLengthMetric.weylScaling_compact_bump_topology
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) {ξ : ℝ}
    (hξ : 0 ≤ ξ) (f : ℂ → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hu : ∀ z, f z ≤ 0)
    (hzero : ∀ x y, weylScaling D ξ 0 x y = ENNReal.ofReal (D x y)) :
    let E : ℂ → ℂ → ℝ := fun x y => (weylScaling D ξ f x y).toReal
    (∀ x, E x x = 0) ∧ (∀ x y, E x y = 0 → x = y) ∧
    (∀ U : Set ℂ, IsOpen U ↔ ∀ x ∈ U, ∃ ε > 0, ∀ y, E x y < ε → y ∈ U) := by
  obtain ⟨c, hl⟩ := exists_lower_bound_of_continuous_compactSupport f hf hc
  exact hD.weylScaling_negative_bump_topology hξ f hl hu hzero

end HarmonicBalls
