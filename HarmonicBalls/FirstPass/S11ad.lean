import HarmonicBalls.FirstPass.S11m.FirstPos
import HarmonicBalls.FirstPass.S11m.ShiftedE1

/-!
# Positivity of the bounded certificate of Lemma 11.12 (route of note §6.2–6.4)

Pieces of the positivity proof that are deterministic or measure-theoretic:

* `exists_E1_shift_pos` (§6.2): on the good box `F` of `exists_pinch_F_pos`, the Weyl-shifted metric by the
  two-bump weight `ξ⁻¹ (log b_Q φ_Q + log b φ_0)` satisfies `E₁` almost surely, so the shifted first event has
  positive probability.
* `exists_const_pos_of_pos` (§6.4): a positive-probability measurable set on which a lower bound `a₂ > 0` and an
  upper bound `d₂ < ∞` hold contains a subset `{a₂ ≥ c, d₂ ≤ d}` of positive probability.

Names follow Armstrong, Kuusi and Mourrat (internal distances) and Duplantier-Sheffield (LQG metric as a Weyl scaling).
-/

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace HarmonicBalls
namespace S11ad

/-- §6.2 of the certificate note. For the good box of `exists_pinch_F_pos`, with `b = K := max 1 (2 (n+1)²)` and
`b_Q = K²`, the Weyl-shifted metric satisfies `E₁` almost surely on the box, hence the shifted first event has
positive probability. -/
theorem exists_E1_shift_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hΩ : ({0} ∪ sphere (0 : ℂ) 5) ⊆ pinchOmegaGeom W Q δ)
    (D : Ω → ℂ → ℂ → ℝ) (hD : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) {ξ : ℝ} (hξ : 0 < ξ) :
    ∃ b bQ : ℝ, 1 ≤ b ∧ 1 ≤ bQ ∧
      ∃ φQ φ0 : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φQ ∧ HasCompactSupport φQ ∧
        (∀ z ∈ closure Q, φQ z = 1) ∧ (∀ z, z ∉ thickening δ Q → φQ z = 0) ∧ (∀ z, φQ z ∈ Icc (0 : ℝ) 1) ∧
        ContDiff ℝ (⊤ : ℕ∞) φ0 ∧ HasCompactSupport φ0 ∧
        (∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) ∧ (∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0) ∧
        (∀ z, φ0 z ∈ Icc (0 : ℝ) 1) ∧
        0 < P {ω | pinchFirstEventLocal (fun x y => (weylScaling (D ω) ξ
          (HarmonicBalls.shiftWeight ξ b bQ φQ φ0) x y).toReal) W T Q' Q δ} := by
  obtain ⟨n, hn⟩ := HarmonicBalls.exists_pinch_F_pos hgeo hΩ D hD
  obtain ⟨φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI, hφ0, hφ0c, hφ01, hφ00, hφ0I⟩ :=
    HarmonicBalls.exists_smooth_pinch_bumps hgeo
  have hδ : 0 < δ := hgeo.delta_pos
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  -- the constants: c₁ = c₃ = 1/(n+1), c₂ = c₄ = n+1, b = K, b_Q = K²
  set K : ℝ := max 1 (2 * ((n : ℝ) + 1) ^ 2) with hK_def
  have hK1 : 1 ≤ K := le_max_left _ _
  have hKk : 2 * ((n : ℝ) + 1) ^ 2 ≤ K := le_max_right _ _
  have hc₁ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hc₂ : (0 : ℝ) < (n : ℝ) + 1 := hn0
  have hb : 2 * ((n : ℝ) + 1) ≤ K * (1 / ((n : ℝ) + 1)) := by
    rw [mul_one_div, le_div_iff₀ hn0]
    nlinarith
  have hbQ : 2 * (K * ((n : ℝ) + 1)) ≤ K * K * (1 / ((n : ℝ) + 1)) := by
    rw [mul_one_div, le_div_iff₀ hn0]
    nlinarith
  have hbQ1 : 1 ≤ K * K := by nlinarith
  have hξ' : 0 < ξ := hξ
  have hae := HarmonicBalls.S11m.ShiftedE1.ae_pinchFirstEventLocal_shiftWeight D hD hgeo hξ' hK1 hbQ1
    hc₁ hc₂ hc₁ hc₂ hb hbQ hφQ hφQc hφQ1 hφQ0 hφQI hφ0 hφ0c hφ01 hφ00 hφ0I
  refine ⟨K, K * K, hK1, hbQ1, φQ, φ0, hφQ, hφQc, hφQ1, hφQ0, hφQI, hφ0, hφ0c, hφ01, hφ00, hφ0I, ?_⟩
  refine lt_of_lt_of_le hn (measure_mono_ae ?_)
  filter_upwards [hae] with ω hω hbox
  obtain ⟨h1, h2, h3, h4⟩ := hbox
  refine hω h1 ?_ h3 ?_
  · exact le_trans h2 (by rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (by linarith))
  · exact le_trans h4 (by rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (by linarith))

/-- §6.4 of the certificate note (choice of `c, d`). If a measurable set `A` has positive probability and on `A` the
lower bound `a₂ > 0` and the upper bound `d₂ < ∞` hold, then for some `c, d > 0` the set `{a₂ ≥ c, d₂ ≤ d} ∩ A` has
positive probability. Continuity from below along the increasing family `S n`. -/
theorem exists_const_pos_of_pos {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A : Set Ω}
    (hAp : 0 < P A) {a₂ : Ω → ℝ} {d₂ : Ω → ℝ≥0∞} (hpos : ∀ ω ∈ A, 0 < a₂ ω ∧ d₂ ω ≠ ∞) :
    ∃ c d : ℝ, 0 < c ∧ 0 < d ∧ 0 < P (A ∩ {ω | c ≤ a₂ ω ∧ d₂ ω ≤ ENNReal.ofReal d}) := by
  set S : ℕ → Set Ω := fun n => A ∩ {ω | 1 / ((n : ℝ) + 1) ≤ a₂ ω ∧ d₂ ω ≤ ENNReal.ofReal ((n : ℝ) + 1)}
    with hS_def
  have hmono : Monotone S := by
    intro m n hmn ω hω
    obtain ⟨hA, h1, h2⟩ := hω
    refine ⟨hA, le_trans ?_ h1, le_trans h2 ?_⟩
    · have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    · exact ENNReal.ofReal_le_ofReal (by
        have hm : (m : ℝ) ≤ n := by exact_mod_cast hmn
        linarith)
  have hcover : A ⊆ ⋃ n, S n := by
    intro ω hωA
    obtain ⟨ha, hd⟩ := hpos ω hωA
    obtain ⟨n₁, hn₁⟩ := exists_nat_one_div_lt ha
    obtain ⟨n₂, hn₂⟩ := ENNReal.exists_nat_gt hd
    refine mem_iUnion.2 ⟨n₁ + n₂, hωA, ?_, ?_⟩
    · have hle : 1 / (((n₁ + n₂ : ℕ) : ℝ) + 1) ≤ 1 / ((n₁ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        push_cast
        have : (0 : ℝ) ≤ n₂ := by positivity
        linarith
      exact le_trans hle hn₁.le
    · have hle : d₂ ω ≤ ENNReal.ofReal (((n₁ + n₂ : ℕ) : ℝ) + 1) := by
        have h1 : d₂ ω ≤ ((n₂ : ℕ) : ℝ≥0∞) := hn₂.le
        refine le_trans h1 ?_
        rw [← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (by push_cast; linarith [(Nat.cast_nonneg n₁ : (0 : ℝ) ≤ n₁)])
      exact hle
  have hunion : P A ≤ ⨆ n, P (S n) := by
    calc P A ≤ P (⋃ n, S n) := measure_mono hcover
      _ = ⨆ n, P (S n) := hmono.measure_iUnion
  have hex : ∃ n, 0 < P (S n) := by
    by_contra hcon
    have hle0 : ∀ n, P (S n) ≤ 0 := fun n => not_lt.1 (fun h => hcon ⟨n, h⟩)
    have : ⨆ n, P (S n) = 0 := le_antisymm (iSup_le hle0) zero_le
    exact absurd (lt_of_lt_of_le hAp (this ▸ hunion)) (lt_irrefl _)
  obtain ⟨n, hn⟩ := hex
  refine ⟨1 / ((n : ℝ) + 1), (n : ℝ) + 1, by positivity, by positivity, ?_⟩
  exact hn

end S11ad
end HarmonicBalls
