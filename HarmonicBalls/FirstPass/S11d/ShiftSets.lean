import HarmonicBalls.FirstPass.S11d.ShiftGeometry
import HarmonicBalls.Proposed.LQG

/-!
# Proposition 11.9, sets and almost-sure bookkeeping

FIRST-PASS NEW. Support lemmas for the assembly of the shifted event (paper lines 3110-3137): closed dyadic squares are
compact and convex (the frozen plane-topology input applies to `K = S₂`); an almost-sure property yields a measurable
subset of a given positive-measure set carrying it, of the same measure; the field σ-algebra of a window is contained in
the ambient σ-algebra (measurable pairings of the whole-plane GFF, `IsWholePlaneGFF.measurable_pairing`).
-/

namespace HarmonicBalls

open Set MeasureTheory Filter Topology

/-- A closed dyadic square (as a set) is closed. -/
theorem isClosed_closedDyadicSquare (n j k : ℤ) : IsClosed (closedDyadicSquare n j k) := by
  unfold closedDyadicSquare
  exact (isClosed_Icc.preimage Complex.continuous_re).inter (isClosed_Icc.preimage Complex.continuous_im)

/-- A convex combination of two reals bounded below by `L`. -/
theorem le_convex_comb {L x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hx : L ≤ x) (hy : L ≤ y) :
    L ≤ a * x + b * y := by
  calc L = a * L + b * L := by rw [← add_mul, hab, one_mul]
    _ ≤ a * x + b * y := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

/-- A convex combination of two reals bounded above by `U`. -/
theorem convex_comb_le {U x y a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hx : x ≤ U) (hy : y ≤ U) :
    a * x + b * y ≤ U := by
  calc a * x + b * y ≤ a * U + b * U := add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    _ = U := by rw [← add_mul, hab, one_mul]

/-- A closed dyadic square (as a set) is convex. -/
theorem convex_closedDyadicSquare (n j k : ℤ) : Convex ℝ (closedDyadicSquare n j k) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    exact le_convex_comb ha hb hab hx1.1 hy1.1
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    exact convex_comb_le ha hb hab hx1.2 hy1.2
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    exact le_convex_comb ha hb hab hx2.1 hy2.1
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    exact convex_comb_le ha hb hab hx2.2 hy2.2

/-- A closed dyadic square is compact. -/
theorem isCompact_closedDyadicSquare_of (n j k : ℤ) : IsCompact (closedDyadicSquare n j k) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_closedDyadicSquare n j k) ?_
  rw [Metric.isBounded_iff_subset_closedBall (0 : ℂ)]
  set s : ℝ := (2 : ℝ) ^ (-n) with hs
  have hs0 : 0 ≤ s := by rw [hs]; positivity
  refine ⟨(|(j : ℝ)| + |((j : ℝ) + 1)| + |(k : ℝ)| + |((k : ℝ) + 1)|) * s, ?_⟩
  intro z hz
  obtain ⟨hre, him⟩ := hz
  have hzre : |z.re| ≤ (|(j : ℝ)| + |((j : ℝ) + 1)|) * s := by
    rw [abs_le]
    obtain ⟨h1, h2⟩ := hre
    have := abs_nonneg (j : ℝ)
    have := abs_nonneg ((j : ℝ) + 1)
    constructor <;> nlinarith [le_abs_self (j : ℝ), neg_abs_le (j : ℝ), le_abs_self ((j : ℝ) + 1),
      neg_abs_le ((j : ℝ) + 1)]
  have hzim : |z.im| ≤ (|(k : ℝ)| + |((k : ℝ) + 1)|) * s := by
    rw [abs_le]
    obtain ⟨h1, h2⟩ := him
    constructor <;> nlinarith [le_abs_self (k : ℝ), neg_abs_le (k : ℝ), le_abs_self ((k : ℝ) + 1),
      neg_abs_le ((k : ℝ) + 1)]
  rw [Metric.mem_closedBall, dist_zero_right]
  have h := Complex.norm_le_abs_re_add_abs_im z
  nlinarith [hzre, hzim]

/-- An almost-sure property holds on a measurable subset of a given set, of the same measure. -/
theorem exists_measurable_subset_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A0 : Set Ω}
    (hA0 : MeasurableSet A0) (p : Ω → Prop) (hp : ∀ᵐ ω ∂P, p ω) :
    ∃ B : Set Ω, MeasurableSet B ∧ B ⊆ A0 ∧ (∀ ω ∈ B, p ω) ∧ P B = P A0 := by
  obtain ⟨t, hsub, htm, ht0⟩ := exists_measurable_superset_of_null (ae_iff.mp hp)
  refine ⟨A0 \ t, hA0.diff htm, sdiff_subset, ?_, measure_sdiff_null ht0⟩
  intro ω hω
  by_contra hb
  exact hω.2 (hsub hb)

/-- The field σ-algebra of an open window is contained in the ambient σ-algebra of the whole-plane GFF. -/
theorem fieldSigmaAlgebra_le {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} {α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc) (U : Set ℂ) :
    fieldSigmaAlgebra α₀ hC U ≤ m := by
  unfold fieldSigmaAlgebra
  refine iSup₂_le fun φ hφ => ?_
  apply Measurable.comap_le
  unfold fieldPairing
  exact (hG.measurable_pairing φ ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩).sub_const _

end HarmonicBalls
